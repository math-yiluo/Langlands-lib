# Sheafification and injectives for actual small-etale transport sheaves

This internal construction uses the actual transport site of
`EtaleTransportSite` and its genuine affine basis from `EtaleTransportAffine`.
The inputs are `Y : Scheme.{u}`, `G : Type w`, a group structure on `G`,
and `ρ : G →* (Aut Y)ᵐᵒᵖ`. Throughout this unit `Small.{u} G` is explicit:
the acting group has a representative in the scheme universe, while its
given universe `w` remains independent.

For the general coefficient constructions, `A : Type uA` has morphisms in
`Type u` and is a concrete category with underlying objects in `Type u`.
It has all limits and colimits of size `(u,u)`. Its forgetful functor
preserves limits and filtered colimits of size `(u,u)` and reflects
isomorphisms. These are precisely the coefficient hypotheses used for the
small-site sheafification construction; this unit makes no assertion for
arbitrary coefficient universes without these hypotheses.

`affineBasis_hasSheafify` applies Mathlib's sheafification on essentially
small sites to the actual affine transport basis. That basis retains all
group-labelled semilinear scheme arrows between its chosen affine
representatives. The already constructed continuous restriction equivalence
then transfers left-exact sheafification to the full transport site, giving
`transport_hasSheafify`.

`sheafify` is the resulting functor on arbitrary transport presheaves,
and `sheafifyAdjunction` is its actual adjunction with the inclusion of
sheaves into presheaves. The functor preserves finite limits. When `A`
is abelian, both the affine and full transport sheaf categories are
abelian, and sheafification is additive. These are Mathlib's sheaf-category
constructions from the established left-exact sheafification.

If `A` is also Grothendieck abelian in universe `u`, Mathlib's
essentially-small-site result makes affine transport sheaves Grothendieck
abelian. The explicit instance
`affineBasis_smallModel_structuredArrow_hasLimits` supplies the limits
for the right Kan extension from the affine basis's small model:
the structured-arrow categories are essentially `u`-small, so the
assumed `(u,u)` limits of `A` suffice. Transporting this structure along
`affineBasisSheafEquiv ρ A`
gives the same property for all transport sheaves. Mathlib's theorem that
Grothendieck abelian categories have enough injectives then provides
`transportSheaf_enoughInjectives`.

For `R : Type u` with a commutative ring structure, `ModuleCat.{u} R`
satisfies the coefficient hypotheses by Mathlib's module-category
constructions. Consequently actual module transport sheaves have enough
injectives. `moduleSheafInjectiveResolution` chooses Mathlib's constructed
injective resolution of each such sheaf in this very category; it is not
an ordinary nonequivariant resolution supplied as input.

The provenance is internal assembly from Mathlib's essentially small-site
sheafification, dense-subsite transfer, abelian sheaf categories,
Grothendieck-category invariance under equivalence and enough-injectives
theorem. It extends the method used for ordinary scheme etale sheaves in
Mathlib's `AlgebraicGeometry/Sites/AffineEtale.lean` and for topological
equivariant sheaves in `Langlands/Sheaf/Equivariant/Abelian.lean`.
No new claim is attributed to Harris or Berkovich.

This unit supplies the sheafification and injective structures needed to
derive the already constructed section representation functor. Actual
derived representation objects and comparison with ordinary etale derived
sections remain successor constructions. Smoothness, compact supports,
analytic spaces, arithmetic coefficients, level towers and Harris
specialization remain separate obligations.
