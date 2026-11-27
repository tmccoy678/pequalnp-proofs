import PEqualNP.Defs

namespace PEqualNP.Outside.ReadOnceDual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Reverse the Boolean order on the monotone gate basis. -/
def orderDualOp : GateOp → GateOp
  | .and => .or
  | .or => .and
  | .not => .not
  | .mod m => .mod m
  | .maj => .maj

def orderDualGate (g : Gate) : Gate :=
  { op := orderDualOp g.op, inputs := g.inputs }

def orderDualCircuit (C : Circuit) : Circuit :=
  { gates := C.gates.map orderDualGate, output := C.output }

theorem not_any_eq_all_not (l : List Bool) :
    (!(l.any id)) = (l.map fun b => !b).all id := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ih]

theorem not_all_eq_any_not (l : List Bool) :
    (!(l.all id)) = (l.map fun b => !b).any id := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ih]

theorem eval_orderDual_and (l : List Bool) :
    GateOp.eval (orderDualOp GateOp.and) (l.map fun b => !b) =
      !(GateOp.eval GateOp.and l) := by
  simpa [orderDualOp, GateOp.eval] using (not_all_eq_any_not l).symm

theorem eval_orderDual_or (l : List Bool) :
    GateOp.eval (orderDualOp GateOp.or) (l.map fun b => !b) =
      !(GateOp.eval GateOp.or l) := by
  simpa [orderDualOp, GateOp.eval] using (not_any_eq_all_not l).symm

theorem eval_orderDual_of_monotone {op : GateOp}
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (l : List Bool) :
    GateOp.eval (orderDualOp op) (l.map fun b => !b) =
      !(GateOp.eval op l) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · exact eval_orderDual_and l
  · exact eval_orderDual_or l

/-- The isolated read-once OR junction has an AND order-dual. -/
theorem readOnceOr_dual (x h : Bool) :
    GateOp.eval (orderDualOp GateOp.or) [!x, !h] =
      !(GateOp.eval GateOp.or [x, h]) := by
  exact eval_orderDual_or [x, h]

theorem orderDualOp_monotone {op : GateOp}
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    orderDualOp op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with rfl | rfl <;> simp [orderDualOp]

theorem size_orderDualCircuit (C : Circuit) :
    (orderDualCircuit C).size = C.size := by
  simp [orderDualCircuit, Circuit.size]

theorem monotone2_orderDualCircuit {C : Circuit} (hC : Monotone2 C) :
    Monotone2 (orderDualCircuit C) := by
  intro g hg
  simp only [orderDualCircuit, List.mem_map] at hg
  obtain ⟨source, hsource, rfl⟩ := hg
  have hs := hC source hsource
  exact ⟨orderDualOp_monotone hs.1, hs.2⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_length (w : List Bool) (g : Gate) :
    (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_map_not (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map fun b => !b).getD i false = !(w.getD i false) := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem step_orderDual (w : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hinputs : ∀ i ∈ g.inputs, i < w.length) :
    step (w.map fun b => !b) (orderDualGate g) =
      (step w g).map fun b => !b := by
  have hvalues :
      g.inputs.map (fun i => (w.map fun b => !b).getD i false) =
        (g.inputs.map fun i => w.getD i false).map fun b => !b := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact getD_map_not w i (hinputs i hi)
  simp only [step, orderDualGate, List.map_append, List.map_singleton]
  rw [hvalues, eval_orderDual_of_monotone hop]

theorem fold_orderDual : ∀ (gs : List Gate) (w : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
    (∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < w.length + j) →
    (gs.map orderDualGate).foldl step (w.map fun b => !b) =
      (gs.foldl step w).map fun b => !b := by
  intro gs
  induction gs with
  | nil => intro w _ _; rfl
  | cons g gs ih =>
      intro w hops hformed
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := hops g (by simp)
      have hgi : ∀ i ∈ g.inputs, i < w.length := by
        intro i hi
        simpa using hformed 0 (by simp) i (by simpa using hi)
      rw [step_orderDual w g hg hgi]
      apply ih
      · intro g' hg'
        exact hops g' (by simp [hg'])
      · intro j hj i hi
        have h := hformed (j + 1) (by simp; omega) i (by simpa using hi)
        rw [step_length]
        omega

def WellFormedOn (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j

theorem wires_orderDualCircuit (C : Circuit) (x : List Bool)
    (hC : Monotone2 C) (hwf : WellFormedOn x.length C) :
    (orderDualCircuit C).wires (x.map fun b => !b) =
      (C.wires x).map fun b => !b := by
  change (C.gates.map orderDualGate).foldl step (x.map fun b => !b) =
    (C.gates.foldl step x).map fun b => !b
  apply fold_orderDual C.gates x
  · intro g hg
    exact (hC g hg).1
  · exact hwf

theorem fold_length : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_length]
      simp
      omega

/-- With an internal output wire, order duality propagates through the whole circuit. -/
theorem eval_orderDualCircuit (C : Circuit) (x : List Bool)
    (hC : Monotone2 C) (hwf : WellFormedOn x.length C)
    (hout : C.output < x.length + C.gates.length) :
    (orderDualCircuit C).eval (x.map fun b => !b) = !(C.eval x) := by
  unfold Circuit.eval
  rw [wires_orderDualCircuit C x hC hwf]
  apply getD_map_not
  change C.output < (C.gates.foldl step x).length
  rw [fold_length]
  exact hout

end PEqualNP.Outside.ReadOnceDual
