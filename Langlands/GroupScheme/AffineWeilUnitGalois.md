# Galois fixed points of the actual scalar-extension Weil unit

Let `L/F` be a finite extension of fields in arbitrary common universe `u`,
and let `G` be an affine group scheme locally of finite type over `F`.
Write `W` for the existing
`AffineWeil.groupScheme F L (AffineWeil.unitBaseChange F L G)`.
Thus the original target and its actual pullback base change are retained.

For each `F`-algebra automorphism `σ` of `L`,
`AffineWeil.unitGaloisAction F L G σ` is an actual ground-field group-scheme
endomorphism of `W`. For every affine test algebra `A`,
`unitGaloisAction_groundPoints` proves that it acts by applying `σ` to the
`L` factor in `L ⊗_F A`, leaving `A` fixed.

When `L/F` is Galois, `mem_range_unit_iff_galois_fixed` proves, on every such
test algebra, the exact equality of the original scalar-extension unit image
with the common fixed subgroup:

```text
q ∈ range (G.affinePointsTarget (AffineWeil.unit F L G) A)
  ↔ ∀ σ : L ≃ₐ[F] L, W.affinePointsTarget (unitGaloisAction F L G σ) A q = q.
```

These statements apply to arbitrary commutative `F`-algebras `A`, including
nonfields and nonreduced algebras. There is no characteristic-zero,
commutativity, connectedness or reductivity assumption on `G`.

This is an internal construction from the published actual scalar-extension
unit, affine Weil corepresentation, multiplicative pullback point comparison,
and `TensorGaloisPoint` descent.

`unitGroundPointsEquiv` composes the canonical affine Weil point equivalence
with the inverse of the actual multiplicative base-change comparison, giving
an equivalence from `W(A)` to the original `G(L ⊗_F A)`.
`unitGaloisPointHom` transports the published tensor coefficient conjugation
through that base-change comparison.
Its naturality follows from coefficient-map naturality of base-change points
and `TensorGaloisPoint.conjugate_naturality`. The resulting natural
endomorphism of the original tensor-valued point functor is represented by
`Corepresented.groupSchemeMap`, which defines `unitGaloisAction`.
The corepresentation's affine-test formula proves
`unitGaloisAction_groundPoints`.

`unitGroundPointsEquiv_unit` identifies the existing unit on every affine
test with the original tensor point extension along `a ↦ 1 ⊗ a`.
The published `TensorGaloisPoint.mem_range_extend_iff` identifies its image
with the common fixed subgroup for a finite Galois extension. Transport
through `unitGroundPointsEquiv` then proves the displayed fixed-image
equivalence on the actual `W` carrier.

The module constructs the family of actual endomorphisms and their
fixed-image characterization. It makes no topological, adelic, rational
quotient or compactness assertion.
