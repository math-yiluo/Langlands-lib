# Affine coordinates under scalar extension

Author: Worker 445.

This internal construction compares relative global sections with scalar
extension. It uses Mathlib's relative spectrum–global-sections adjunction and
its tensor-product description of a pullback of affine spectra. The
construction is derived from these categorical universal properties; it does
not assert a new statement from external literature.

Fix a commutative ring `R` in an arbitrary universe and an affine object `X`
over `Spec R`. Write `A` for the commutative `R`-algebra
`((algΓ R).obj X).unop`. For any commutative `R`-algebra `B`,
`baseChangeSectionsIso X B` identifies the coordinate algebra of
`X ×[Spec R] Spec B`, viewed over `Spec B`, with `B ⊗[R] A` as a
commutative `B`-algebra.

The intermediate constructions have these meanings:

- The reused `AffineClosedFactorizationLocus.coordinateIso R X` is the unit
  of the relative adjunction, exhibited as an
  isomorphism because the essential image of relative spectrum is precisely
  the affine objects.
- The reused `Langlands.GroupScheme.Corepresented.affineSectionsIso A` is the
  inverse, after removing the opposite category, of the counit isomorphism.
  Relative spectrum is fully faithful.
- `tensorSpecIso B A` identifies the base change of the relative spectrum of
  `A` with the relative spectrum of `B ⊗[R] A`. Its underlying scheme
  isomorphism first swaps the pullback factors and then uses
  `pullbackSpecIso R B A`. The first projection of the latter is the structure
  map to `Spec B`, so the isomorphism respects the specified base.
- `baseChangeModelIso X B` applies pullback to `coordinateIso R X` and then
  composes with `tensorSpecIso B A`.
- Applying relative global sections contravariantly and composing with
  `affineSectionsIso` gives `baseChangeSectionsIso X B`.

Finally, `projective X B` transports projectivity along the linear equivalence
underlying that algebra isomorphism. Its sole module premise is
`Module.Projective B (B ⊗[R] A)`, and its conclusion is projectivity of the
actual relative coordinate algebra of the base-changed object. No finite
generation, finite presentation, flatness or faithful flatness is required
for these comparisons. In the host proof the algebra `B` will additionally
be faithfully flat, as supplied by `HasFpqcProjectiveCoordinateModule`.

The implemented proof checks the structure map of `tensorSpecIso` using the
projection identities for `pullbackSpecIso` and `pullbackSymmetry`. The
remaining isomorphisms are compositions and images of adjunction
isomorphisms, and the last theorem uses `Module.Projective.of_equiv'`.
This module supplies the coordinate transport needed for the scalar-extension
step; it does not construct the final closed-factorization locus.
