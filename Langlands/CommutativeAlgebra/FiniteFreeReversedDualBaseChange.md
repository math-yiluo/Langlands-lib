# Scalar extension of reversed dual complexes

Author: Worker 1015.

For commutative rings `R,S`, any ring homomorphism `φ : R →+* S`,
any integer `g`, and a cochain complex `C` whose terms are finite free,
`reversedDualBaseChangeIso` constructs an actual isomorphism

```
(baseChange φ).obj (reversedDual g C) ≅
  reversedDual g ((baseChange φ).obj C).
```

There is no flatness or boundedness hypothesis on this isomorphism.
Its component in degree `i` is Mathlib's
`IsBaseChange.toDualBaseChange`, applied to the canonical map from
`C.X (g-i)` to its tensor product with `S`. Finite freeness ensures that
this comparison is an equivalence. On pure tensors, evaluation of the
functional associated to `s ⊗ f` at `1 ⊗ x` is `s * φ (f x)`.
Checking this formula on the canonical generators proves compatibility
with the transposed differentials.

`isZero_homology_baseChange_reversedDual_of_acyclic` additionally assumes
that `C` is bounded finite free and that its scalar extension is acyclic.
Scalar extension gives a bounded above complex of projective modules.
The contracting-homotopy result in `FiniteFreeReversedDualExactness`
therefore makes its reversed dual acyclic. The displayed isomorphism
transports vanishing back to the scalar extension of the original
reversed dual.

This is internal supporting algebra, proved using Mathlib's finite free
dual base-change equivalence, the existing perfect-complex scalar
extension lemmas, and the reversed-dual contraction. No localization
support theorem or punctual complex conclusion is asserted here.
