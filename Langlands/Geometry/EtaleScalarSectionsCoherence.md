# Scalar identity and composition on ordinary section actions

This module proves that the canonical ordinary global-section comparison for
scalar restriction respects the identity and composition comparisons already
constructed on actual étale sheaves. It constructs the corresponding
comparisons on modules with group actions and proves the same compatibility
for the ordinary section actions of geometric equivariant sheaves.

## Provenance and parameters

This is an internal construction from
`Langlands.Geometry.EtaleScalarCoherence` and its imported
`EtaleScalarRestriction` and `EtaleDerivedSections` constructions.
It also uses Mathlib's `Functor.mapActionCongr` and `Functor.mapActionComp`.
No external literature theorem is transcribed, and no scalar comparison
or compatibility equation is assumed.

The rings `R`, `A`, and `B` are commutative rings in `Type u`;
`φ : R →+* A` and `ψ : A →+* B` are arbitrary ring homomorphisms.
The scheme `X : Scheme.{u}` and all section-module carriers have the
same universe `u`. No injectivity, surjectivity, or flatness of these maps
is required.

The group `G : Type t` has no supplied topology. The action comparisons on
modules use arbitrary algebraic `G`-actions. For the equivariant sheaf results,
the supplied action is `ρ : G →* (Aut X)ᵐᵒᵖ`, with the Library convention
`aut ρ (g * h) = aut ρ g ≪≫ aut ρ h`.
The coefficients are actual geometrically equivariant sheaves of modules
on the small étale site of `X`.

All declarations lie in
`Langlands.Geometry.EtaleCohomologyAction`.

## Canonical ordinary-section compatibility

Write `T_φ` for `sheafRestrictScalars φ X`, `r_φ` for
`ModuleCat.restrictScalars φ`, and `Γ_R` for
`EtaleDerivedSections.sections X R`. The functor `Γ_R` is Mathlib's
global-section functor from the constant-sheaf adjunction.
The existing natural isomorphism `e_R = EtaleDerivedSections.sectionsIso X R`
identifies it with evaluation at the terminal object of the small étale site.

The existing `scalarRestrictionSectionsIso φ` is the comparison

```text
σ_φ(F) : Γ_R(T_φ F) ≅ r_φ(Γ_A F).
```

Its forward map is `e_R(T_φ F).hom ≫ r_φ(e_A(F).inv)`.
These canonical maps are used in all equations below; they are not replaced
by identities.

The theorem `scalarRestrictionSections_id X F`, for an `R`-module sheaf, proves

```text
Γ_R((sheafRestrictScalarsIdIso X).hom.app F)
  = σ_id(F).hom ≫ (ModuleCat.restrictScalarsId R).hom.app (Γ_R F).
```

Both sides go from sections of the identity-restricted sheaf to the original
section module. The proof uses `NatIso.naturality_2` to express the left side
through terminal evaluation. The resulting equality is the naturality of
the module identity comparison with respect to `e_R(F).inv`.

The theorem `scalarRestrictionSections_comp φ ψ X F`, for a `B`-module sheaf,
proves the equality

```text
Γ_R((sheafRestrictScalarsCompIso φ ψ X).hom.app F)
  ≫ σ_φ(T_ψ F).hom ≫ r_φ(σ_ψ(F).hom)
  = σ_(ψ.comp φ)(F).hom
      ≫ (ModuleCat.restrictScalarsComp φ ψ).hom.app (Γ_B F).
```

Its common source is `Γ_R(T_(ψ.comp φ) F)` and its common target is
`r_φ(r_ψ(Γ_B F))`. The left route first splits scalar restriction on the
sheaf and then applies the two canonical section comparisons. The right
route first applies the section comparison for the composite ring map and
then splits module scalar restriction.

The proof again transports the sheaf map through `e_R`. It expands the
canonical section comparisons, uses preservation of composition by scalar
restriction, and cancels adjacent inverse/forward components of the
evaluation isomorphisms, including those under `r_φ`. The module composition
comparison preserves elements, so the remaining maps agree by their
definitions. This proof uses ordinary sections only.

## Comparisons on modules with group actions

The definition `actionRestrictScalarsIdIso G` constructs

```text
(ModuleCat.restrictScalars (RingHom.id R)).mapAction G ≅ 𝟭.
```

It applies `Functor.mapActionCongr` to the module identity comparison.
The definition `actionRestrictScalarsCompIso φ ψ G` constructs

```text
(ModuleCat.restrictScalars (ψ.comp φ)).mapAction G
  ≅ (ModuleCat.restrictScalars ψ).mapAction G
      ⋙ (ModuleCat.restrictScalars φ).mapAction G.
```

It first lifts the module composition comparison with
`Functor.mapActionCongr` and then applies `Functor.mapActionComp`.
Both are natural isomorphisms of actual action categories, with intertwining
proved by the imported functor constructions.

The four lemmas ending in `hom_app_hom` and `inv_app_hom` identify the
underlying module maps in both directions with the corresponding Mathlib
module comparisons. For composition, the extra identity component of
`mapActionComp` is removed using the category identity laws.

## Compatibility with geometric section actions

The theorem `scalarRestrictionSectionsFunctor_id` is the identity equation
above in `Action (ModuleCat R) G`: applying `pullbackSectionsFunctor` to
`scalarRestrictionIdIso` agrees with the canonical
`scalarRestrictionSectionsFunctorIso` followed by
`actionRestrictScalarsIdIso`.

The theorem `scalarRestrictionSectionsFunctor_comp` is the composition
equation in that action category. Its left route applies sections to
`scalarRestrictionCompIso`, then the two ordinary-section action comparisons;
its right route applies the comparison for the composite ring map, then
`actionRestrictScalarsCompIso` on the original section action.

Each proof uses `Action.Hom.ext`, the published formula for
`pullbackSectionsFunctor` on coefficient morphisms, and the corresponding
ordinary module equation established above. Thus the equations retain the
geometric group actions as well as the section maps.

## Scope

The construction concerns ordinary global sections on one supplied scheme.
Compatibility on varying-scheme coefficient diagrams, derived scalar
comparisons, preservation of injectives, tensor extension, ideal reduction,
inverse limits, smoothness, analytic sites, compact supports, and Harris
specialization remain separate obligations.
