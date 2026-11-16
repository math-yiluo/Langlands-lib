# Cocycle vanishing for finite vector-bundle series

This internal deduction proves cocycle vanishing for an affine group scheme
`H` over an arbitrary affine scheme `S`, in every universe `u`, supplied with
the actual finite normal series of `RelativeUnipotent.Basic`. Its quotients
are represented additive groups of finite locally free module sheaves, with
the natural all-test section coordinates required there. A global free basis
for these module sheaves is not assumed.

`HasVectorBundleSeries.cocyclesVanish` proves the arbitrary-base predicate
`AffineCocycle.CocyclesVanish H`: after every base change to an affine test
scheme `T` over `S`, every cocycle on an affine flat surjective cover of `T`
is trivial. These covers need not be locally of finite presentation. The
finite-length wrapper takes an existential series length.

The proof is induction on that length. At length zero, the all-test
identity image is the trivial subgroup functor, and the generic
trivial-group lemma applies. At a successor, the closed kernel of the
represented fppf vector-bundle quotient is affine. Induction proves its
cocycle vanishing. Both the original group and the vector-bundle quotient
are affine over the affine base, so the generic quotient-section lemma
gives a section as a morphism of schemes over `S`. Vector-bundle cocycle
vanishing after every affine base change supplies the quotient case.
The generic extension lemma then lifts a quotient primitive along the
section, twists the cocycle into the kernel, and applies kernel vanishing.
This does not require the scheme section to be a group homomorphism.

`Cocycle.isTrivial_of_hasFiniteVectorBundleSeries` removes the identity
base change and gives triviality for the original group on any affine
flat surjective cover. The fppf variant allows an arbitrary single flat,
surjective, locally finitely presented cover of the affine base. Its total
space need not be affine or quasi-compact. It applies the existing affine
fppf refinement and original-cover reflection theorem. The corresponding
base-change variant gives the same conclusion over every affine test
scheme over `S`.

`Cocycle.vectorBundleSeriesFppfCochain` chooses the morphism `U ⟶ H.X` from
this original-cover existential. Its specification states, for every
scheme `Z` over `S` and every `a,b : Z ⟶ U`,
`ξ(a,b) = (a ≫ f) * (b ≫ f)⁻¹`. The equation is not restricted to affine
or geometric tests.

The internal provenance is the series induction of `AffineVectorSeries`,
now using `VectorBundleBaseChangeCocycle` for actual locally free sheaves
and the arbitrary-base reductions of `AffineCocycleReduction`. The cover
extension uses `CocycleAffineRefinement`. This module assumes the series
and the affineness of `H`; it does not construct a filtration from geometric
unipotence or Borel data, a quasi-split model, or a Weil-restriction
presentation, and it does not prove the reductive inner-form target.
