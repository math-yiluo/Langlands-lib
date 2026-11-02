# Corepresented coordinates for arbitrary affine group schemes

This internal construction adapts the published `Corepresented` interface to an
arbitrary affine group scheme over the spectrum of a commutative ring. No
smoothness, finite type or field hypothesis is used.

For an algebra cogroup `C`, `Corepresented.cogroupFunctor` is its group-valued
Yoneda presheaf, reindexed as a covariant functor of algebras. Opposite algebra
homomorphisms give `cogroupCorepresentation`. Applying the fully faithful
group-valued Yoneda embedding to `Corepresented.pointsIso` gives the actual
cogroup isomorphism `cogroupRecoveryIso`.

For an affine group scheme `G`, pinned Mathlib's essential-image theorem for
`algSpec` and its lift to group objects supplies a chosen algebra cogroup and an
isomorphism from its spectrum to `G`. The namespace `AffineCoordinates` packages
this as `algebra`, `functor`, `corepresentation` and `groupSchemeIso`.
The last object is an isomorphism in the category of group schemes, so it
preserves all group operations.

The choice of coordinate algebra is noncanonical. This module does not identify
it with the global-sections algebra, and does not assert a definitional equality
between the reconstructed group law and the original one. The explicit
isomorphism is the transport interface.

The provenance is an internal derivation from the published Corepresented
construction and pinned Mathlib's `essImage_algSpec`,
`Functor.essImage_mapGrp`, and `yonedaGrpFullyFaithful`. No external
structural theorem is added.
