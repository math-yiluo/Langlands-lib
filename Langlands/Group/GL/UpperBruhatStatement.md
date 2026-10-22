# Upper triangular Bruhat factorization over a field

Authors: Worker 96 and Worker 6 (statement interface and consumer design).

`Langlands.GeneralLinear.FieldUpperBruhatFactorizationTheorem.{u}` is a
closed, transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatStatement`. This module states the proposition;
it provides no proof of it.

For every field `K : Type u`, every natural rank `n`, and every actual
invertible matrix `g : Langlands.GeneralLinear n K`, the proposition asks for
invertible matrices `a` and `b` and an actual permutation
`w : Equiv.Perm (Fin n)` such that

```text
(∀ i j : Fin n, j < i → a i j = 0) ∧
(∀ i j : Fin n, j < i → b i j = 0) ∧
g = a * Langlands.GeneralLinear.permutation n K w * b.
```

The entrywise conditions say that both outer factors are upper triangular.
Their invertibility is part of their type; their diagonal entries need not
equal one. All field universes and all ranks, including zero, are quantified
inside the proposition. No topology, valuation, characteristic restriction,
algebraic closure, or positive-rank hypothesis is required. The caller supplies
no factorization certificate, adapted basis, pivot condition, or matrix
reduction. The existential witnesses are the conclusion to be proved.

The module imports the existing `Langlands.Group.GL.Basic` and
`Langlands.Group.GL.Maps` unchanged. It uses their actual invertible matrices
and `GeneralLinear.permutation n K w`, whose entry at `(i,j)` is
`if w j = i then 1 else 0`; thus the permutation matrix sends `e_j` to
`e_(w j)`.

## Internal provenance and intended use

This is an internal algebraic prerequisite designed for the published
`Langlands.Geometric.PadicBruhatMatrixExistenceTheorem` in
`Langlands.Representation.Geometric.BruhatMatrixStatement`. It is stronger in
scope than that p-adic parabolic representative-existence target: it ranges
over arbitrary fields and all ranks, and requests a factorization with two
upper triangular invertible factors.

The intended deduction specializes to the p-adic coefficient field, uses the
separate inclusion of upper triangular matrices in the ordered upper block
parabolics, and passes to the parabolic double-coset quotient. If the present
factorization supplies `w`, the consumer uses the inverse permutation `w⁻¹`,
since `permutation n K (w⁻¹)` inverted equals `permutation n K w`. The inclusion
and quotient deduction are separate proof obligations; this module proves
neither. It also asserts no uniqueness or Weyl-class reflection.

This formulation comes from the project's proof decomposition and the
consumer's existing permutation convention. It is not claimed to be a
verbatim statement from Bernstein and Zelevinsky (1977), nor to follow merely
by extending their p-adic hypotheses to arbitrary fields. Original-source
provenance for the existing p-adic target remains in its published paired
Markdown. This internal prerequisite has no external source claim and still
requires a separate proof of factorization existence.
