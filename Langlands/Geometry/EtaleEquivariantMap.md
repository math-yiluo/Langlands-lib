# Geometric maps on equivariant ordinary étale cohomology

This module constructs the map on ordinary small-étale cohomology associated
with an étale equivariant scheme morphism and a compatible morphism of actual
coefficient sheaves. It proves equivariance in every natural-number degree,
compatibility with source and target coefficient morphisms, and compatibility
with the canonical identification of degree-zero cohomology with global sections.

## Inputs and conventions

`X` and `Y` are schemes in universe `u`; `R : Type u` is a commutative ring.
The coefficient category on either scheme is the published category of sheaves
of `ModuleCat.{u} R` on its small étale site. The group `G : Type w` has an
independent universe and no topology. Its actions are encoded by
`ρ : G →* (Aut X)ᵐᵒᵖ` and `τ : G →* (Aut Y)ᵐᵒᵖ` using the existing opposite
automorphism convention. Write `σ_g = aut ρ g` and `υ_g = aut τ g`.

The morphism `f : Y ⟶ X` is étale. Its equivariance is the equation
`f ≫ σ_g.hom = υ_g.hom ≫ f` for every `g`. Composition is in Lean's order:
`a ≫ b` first applies `a`. Thus pullback on cohomology goes from `X` to `Y`.

The input coefficients `F` and `E` are the published translation-equivariant
module sheaves on `X` and `Y`, respectively. Their structure maps are
`F.act g : σ_g* F ⟶ F` and `E.act g : υ_g* E ⟶ E`. The symbol `*` here denotes
the actual étale restriction functor from `EtalePullback`, given by precomposition
on small étale sites.

## The geometric and coefficient squares

`equivariantRestrictionIso` constructs

`σ_g* ⋙ f* ≅ f* ⋙ υ_g*`.

It first identifies successive restrictions with restriction along
`f ≫ σ_g.hom`, transports along the supplied geometric equivariance equation,
and then uses the inverse composition comparison for `υ_g.hom ≫ f`.
The input is an equality of actual scheme morphisms, and all three comparisons
are already constructed in the published restriction framework.

`GeometricCoefficientMap R ρ τ f hf F E` consists of a sheaf morphism
`α.hom : f* F ⟶ E` satisfying, for each `g`,

`f*(F.act g) ≫ α.hom = square_g.hom_F ≫ υ_g*(α.hom) ≫ E.act g`.

This is compatibility of coefficient sheaves. No cohomology object, map,
equivariance law, or comparison theorem is supplied as a field.
`comp_coefficient` rewrites this square after identifying the composite
restriction functors; its proof cancels the composition isomorphism.

## Cohomology and sections

`GeometricCoefficientMap.cohomologyMap α q` is a morphism in
`Action (ModuleCat.{u} R) G` from `pullbackCohomologyAction R ρ F q` to
`pullbackCohomologyAction R τ E q`. By `cohomologyMap_hom`, its underlying map is
exactly `EtalePullback.cohomologyMapWithCoefficients f R q α.hom`:
the constructed geometric pullback followed by the ordinary cohomology map of
`α.hom`.

The equivariance proof expands both action maps using their published geometric
formulas. The composition theorem rewrites each side as the cohomology map of a
composite scheme morphism with its composite coefficient map.
`comp_coefficient` identifies the coefficient maps; `cohomologyMap_congr`
transports across the geometric equivariance equation. This derives the action
compatibility from the sheaf square.

`precomp α β`, for an equivariant coefficient map `β : F' ⟶ F`, has underlying
map `f*(β.hom) ≫ α.hom`. Its coefficient square follows from the square for `α`,
equivariance of `β`, and naturality of `equivariantRestrictionIso`.
`postcomp α β`, for `β : E ⟶ E'`, has underlying map `α.hom ≫ β.hom`; its square
uses equivariance of `β`. The lemmas `cohomologyMap_precomp` and
`cohomologyMap_postcomp` prove the corresponding composition formulas for action
morphisms. These are coefficient compositions on the two fixed schemes.

`sectionsMap α` transports `cohomologyMap α 0` through the existing canonical
equivariant degree-zero isomorphisms. The theorem `cohomologyMap_zero` states
the resulting commuting square. `sectionsMap_hom` identifies the underlying map
with ordinary global-section restriction along `f` followed by global sections
of `α.hom`. Its proof applies the degree-zero square, naturality in the
coefficient morphism, and the published degree-zero formula for geometric
pullback, cancelling the canonical isomorphism. Finally,
`sectionsMap_precomp` and `sectionsMap_postcomp` give the same two coefficient
composition laws on global sections.

## Provenance and scope

This is an internal construction from `EtaleActionFunctor`,
`EtaleAutomorphismPullback`, `EtaleCohomologyDiagram`, and
`EtaleDerivedPullbackFunctoriality`. It introduces no additional claim from the
Harris or Berkovich literature. The underlying cohomology is the existing right
derived global-section functor on actual module sheaves; the maps use its
published geometric pullback construction.

The schemes, group actions, equivariant étale morphism, and compatible coefficient
map are inputs. This module does not construct a canonical equivariant pullback
sheaf from `F`, nor composition of geometric maps between three schemes. It does
not construct Harris spaces or level maps, a Hecke pushforward or trace,
compactly supported cohomology, smooth actions, analytic sites, or comparisons
with the Harris complexes. Those remain separate parts of the framework.
