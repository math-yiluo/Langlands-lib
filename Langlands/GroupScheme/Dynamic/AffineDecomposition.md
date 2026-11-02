# Limit, kernel and multiplication for the constructed affine dynamic subgroups

Let `R` be any commutative ring, let `F` be a group-valued functor on
commutative `R`-algebras corepresented by `B`, and let
`χ : G_m → Corepresented.groupScheme F e` be an actual cocharacter.
This module supplies the limit homomorphism, its kernel and the multiplication
isomorphism for the explicit quotient schemes constructed in
[`Representability`](Representability.md). There are no representation
hypotheses in these specializations.

## Provenance and implementation

This is an internal specialization of
[`SchemeDecomposition`](SchemeDecomposition.md). That module constructs the
scheme maps for represented dynamic subgroups of a separated group scheme.
Here the representations are the proved `isRepresentedBy_parabolicHom`,
`isRepresentedBy_centralizerHom` and `isRepresentedBy_unipotentHom`.
Affineness of `Spec B` supplies separatedness of its structure morphism.
No new result from the literature is asserted.

All declarations are in `Langlands.GroupScheme.Corepresented`.

- `limitGroupHom χ : parabolicScheme χ → centralizerScheme χ` is the limit
  at zero. `limitGroupHom_comp` identifies its composite into the ambient
  group with `Dynamic.limit` on every test scheme.
- `centralizerToParabolic χ` is the inclusion.
  `centralizerToParabolic_comp` identifies its composite with `parabolicHom`
  as `centralizerHom`. `centralizerToParabolic_comp_limitGroupHom` proves
  that it is a section of the limit homomorphism.
- `unipotentIsoKernel χ` is an isomorphism of group schemes from the
  constructed `unipotentScheme χ` to the existing scheme-theoretic kernel
  of `limitGroupHom χ`. `unipotentIsoKernel_hom_comp` records compatibility
  with the inclusions into the original group scheme.
- `multiplicationIso χ` is an isomorphism in `Over (Spec R)` from
  `unipotentScheme χ × centralizerScheme χ` to `parabolicScheme χ`.
  `multiplicationIso_hom_comp` proves that its map into the ambient group
  is multiplication, with the unipotent factor first.
  `lift_comp_multiplicationIso_hom_comp` computes the same map on a pair
  of arbitrary test points by the product pairing and distribution of
  precomposition over multiplication.
- `multiplicationIso_inv_snd` and `multiplicationIso_inv_fst_comp`
  specialize [`SchemeCoordinates`](SchemeCoordinates.md): the inverse's
  centralizer coordinate is `limitGroupHom`, and its unipotent coordinate
  followed into the ambient group is `p · (lim p)⁻¹`.

The quotient schemes here are the spectra of `B` modulo the explicit coaction
coefficient ideals of `Representability`. The results concern all test schemes,
including nonreduced ones, over an arbitrary commutative base ring. No finite
presentation, smoothness, reductivity, field or topology assumption is used.
The multiplication is an isomorphism of schemes over the base; this module does
not construct a semidirect product group object on the fibre product.
