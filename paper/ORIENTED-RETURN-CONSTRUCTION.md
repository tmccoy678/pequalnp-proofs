# The Oriented Return Construction

**Taylor Westfall-McCoy and Blu Private**  
**26 November 2026**

## 1. The law

Let

\[
U_{18}=(1,5,7,11,13,17)
\]

with cyclic gaps \(4,2,4,2,4,2\). Let \(T\) advance one port, \(M\) reverse
orientation, and \(I\) be identity. The canonical Lean development proves

\[
T^6=I,\qquad M^2=I,\qquad MTM=T^{-1}.
\]

These are finite equalities, checked without `sorry` or added axioms.

## 2. The return cell

For Boolean variables \(p,q,r,a,b,d,c,e,f\), define

\[
S=
p(a\lor b\lor c)
\lor q(a\lor d\lor e)
\lor r(b\lor d\lor f).
\]

The direct fan-in-two construction of \(S\) uses eleven gates. A measured
ten-gate near-circuit has exactly two defects: the forbidden diagonals
\((6,7)\) and \((1,8)\), each accounting for eighteen false positives in the
full 14-input table. The two error sets are disjoint.

The remaining finite question is therefore exact:

> Does a ten-gate fan-in-two AND/OR/NOT circuit compute \(S\)?

No particular solver is part of the theorem. The public SAT instance is one
method of searching for the circuit.

## 3. Constructive theorem

Let \(F\) be the edge function of the 14-vertex Heawood incidence graph with
point neighborhoods

```text
0: 7 8 10       1: 7 9 13       2: 8 12 13
3: 7 11 12      4: 10 11 13     5: 9 10 12
6: 8 9 11
```

> **Theorem.** If a ten-gate fan-in-two AND/OR/NOT circuit computes \(S\), then
> a 26-gate fan-in-two AND/OR/NOT circuit computes \(F\).

**Proof.** Map the three terms of \(S\) to point stars \(0,1,6\). Compute the
four untouched point stars \(2,3,4,5\), using three gates per star. Join the
output of the return cell with the four untouched star outputs, using four OR
gates. The total is

\[
10+4\cdot3+4=26.
\]

The seven point stars partition the 21 listed edges, so their disjunction is
exactly \(F\). ∎

## 4. Certification

An explicit ten-gate cell is finite data. The published assembler expands it
to 26 gates and evaluates every one of the \(2^{14}=16,384\) inputs. A witness
is emitted only at zero error. Lean then checks fan-in, size, and equality with
the posted function by kernel reduction.

Thus any successful construction method gives a short machine-checkable proof
of the finite circuit theorem.

## 5. Uniform continuation

The checked meta-complexity library identifies the global bridge: a uniform
polynomial-time reduction from SAT to the last-gate problem, satisfying the
minimal and one-gate-above-minimum promises on every input, connects that
problem to \(P=NP\).

The oriented return construction supplies one exact finite building block for
that program. Completing the global proof requires extending the construction
uniformly and proving the reduction and its runtime bound. That is the next
mathematical theorem, not a task delegated to a particular SAT solver.

## 6. Public record

- Lean-verified law:
  <https://github.com/tmccoy678/riemann-green-spiral/pull/12>
- Frozen pre-result construction:
  <https://github.com/tmccoy678/oriented-six-port-law/releases/tag/v0.5.0>
- Reproducibility verification:
  <https://github.com/tmccoy678/oriented-six-port-law/actions/runs/45913681949>

The exact search instance was published before its verdict. The theorem above
is independent of whether CaDiCaL, another solver, or a direct construction
first supplies the ten-gate cell.
