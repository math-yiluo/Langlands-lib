# Vector-bundle cocycles after arbitrary affine base change

Let `b : T → S` be a morphism of schemes in an arbitrary universe `u`, and let `M`
be a sheaf of modules on `S`. For a test scheme `Z → T`,
`baseChangeSectionEquiv b M Z` is the additive equivalence

`Γ(Z, Z^*(b^*M)) ≃+ Γ(Z, (Z → T → S)^*M)`.

It is induced by the canonical composition isomorphism for sheaf pullback,
evaluated on global sections. No affine or quasi-coherent hypothesis is needed
for this equivalence.

`baseChangeSectionEquiv_naturality` states that it intertwines the actual
`RelativeUnipotent.sectionPullback` maps for every morphism `W → Z` over `T`.
These maps include the pullback composition and equal-map comparisons.
`baseChangeSectionEquiv_symm_naturality` gives the same identity for the inverse
equivalence.

Suppose a group scheme `V` over `S` is supplied with natural all-test
multiplicative identifications of its points with the additive sections of
pullbacks of `M`. `baseChangeSectionPointsEquiv` first applies the pullback
adjunction on group points, then these identifications, and finally the inverse
section comparison. It therefore gives the analogous coordinates for the
base-changed group, with coefficient sheaf `b^*M` on `T`.
`baseChangeSectionPointsEquiv_naturality` proves their naturality for every test
scheme over `T`.

`AffineVectorBundleCocycle.cocycle_isTrivial_baseChange` assumes that `T` is
affine and that `V` satisfies the published `IsVectorBundleAdditive` predicate.
For any affine flat surjective cover `U → T`, every cocycle with values in
`V ×[S] T` is trivial: there is one morphism `f : U → V ×[S] T` satisfying

`ξ(a,c) = (a ≫ f) * (c ≫ f)⁻¹`

for every test scheme `Z → T` and every `a,c : Z → U`. Neither `S` nor the test
scheme `Z` needs to be affine. The cover need not be of finite presentation.

## Implemented proof

The section comparison is an additive equivalence because the pullback
composition map is an isomorphism of module sheaves. Its naturality follows by
evaluating `RigidifiedModule.compHom_assoc` on global sections and using
`Langlands.Scheme.Modules.sectionPullback_naturality`.
`pullbackSection_eq_sectionPullback` identifies the section maps used by the two
interfaces. Applying the inverse equivalence proves inverse naturality.

The group coordinates compose `baseChangePointsEquiv` with the given
coordinates and the multiplicative version of the inverse additive comparison.
Naturality follows from the preceding section identity, the original coordinate
naturality and the pullback adjunction's naturality on points.

For the final theorem, local bases for `M` make it locally free, hence
quasi-coherent. The pullback sheaf `b^*M` is quasi-coherent. The new coordinates
turn the group cocycle into a `SectionCocycle` with these coefficients.
`SectionCocycle.exists_coboundary` supplies a single section over `U`.
Applying the inverse group coordinates to this section produces `f`; applying
the coordinates to the required equation proves it from the section coboundary
identity.

## Provenance and scope

This is internal derived content. The inputs are the canonical sheaf pullback
comparisons and their associativity, actual section-pullback naturality, the
group pullback adjunction and the quasi-coherent section-cocycle theorem in
`RelativeUnipotent.AffineVectorBundleCocycle`.

The theorem supplies the vector-bundle case needed for induction on a supplied
finite series. This module does not construct such a series, prove the series
induction, construct Borel quotients or special quasi-split models, or prove the
semilocal quasi-split inner-form target.
