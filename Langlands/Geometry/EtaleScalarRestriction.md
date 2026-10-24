# Scalar restriction of equivariant etale sheaves

## Scope and provenance

This is an internal construction extending the Library's actual small-etale
sheaves and geometric translation actions. It uses
`ModuleCat.restrictScalars` and `sheafCompose` from Mathlib, together with
`EtaleDerivedSections`, `EtalePullback`, `EtaleCohomologyAction`,
`EtaleActionFunctor`, and `EtaleEquivariantPullback`. No theorem from Harris or
another external source is being transcribed.

Let `R` and `S` be commutative rings in universe `u`, let `φ : R →+* S`, and
let `X` be a scheme in universe `u`. Section modules also have universe `u`.
Let `G` be a group in an independent universe `w`, with supplied action
`ρ : G →* (Aut X)ᵐᵒᵖ`. We use the existing opposite-automorphism convention:
`aut ρ (g * h)` is `aut ρ g` followed by `aut ρ h`. The translation functor
`T_g` is restriction along the scheme automorphism `aut ρ g`.
An equivariant coefficient sheaf has structure maps `T_g F → F` with the
published unit and product laws.

Everything here concerns ordinary sheaves on the small-etale site and
algebraic group actions. No topology or smoothness is imposed on `G`.
The ring homomorphism need not be injective, surjective or flat.

## Sheaves and equivariant coefficients

`sheafRestrictScalars φ X` is the functor from `S`-module sheaves to
`R`-module sheaves obtained by postcomposing with
`ModuleCat.restrictScalars φ`. For every etale object `U`, its section module
has the same additive group as `F(U)`, with scalar multiplication

```
r • m = φ(r) • m.
```

Restriction maps and morphisms retain their underlying additive maps.
Mathlib supplies the sheaf property: module restriction of scalars is a right
adjoint in these universes, hence preserves the limits needed for
`sheafCompose`. No sheafification is chosen. The sheaf functor is faithful by
Mathlib's faithful scalar-restriction and sheaf-composition instances.

`scalarRestrictionTranslateIso` compares translation then scalar restriction
with scalar restriction then translation. It is the identity comparison,
because these two operations give the same section modules and maps.

`scalarRestrictionObj` equips the restricted sheaf with the restricted maps
`F.act g`. Its unit and product laws are proved by applying the original laws,
then checking the comparison morphisms on each section module and using
preservation of composition. These are derived construction fields, not supplied
compatibility assumptions.

`scalarRestrictionFunctor` sends equivariant coefficient morphisms to their
scalar restrictions. Their equivariance follows by applying the sheaf functor
to the original commutative square. Identity and composition follow from that
functor's laws. The resulting functor is faithful, since equality of restricted
morphisms can be tested on their underlying sheaf maps.
`scalarRestrictionForgetIso` identifies forgetting equivariance after scalar
restriction with restricting the underlying sheaf.

## Geometric restriction

For the following constructions, supply another scheme `Y` in universe `u`,
an action `τ : G →* (Aut Y)ᵐᵒᵖ`, an etale morphism `f : Y ⟶ X`, and the
geometric equivariance equations

```
f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f.
```

`scalarRestrictionPullbackIso` compares the two orders of ordinary geometric
restriction and coefficient scalar restriction. Its components are identities.
Here geometric restriction means evaluating an `X`-sheaf on the composite of an
etale `Y`-object's structure map with `f`.

`scalarRestriction_equivariantRestrictionIso_inv` shows that the inverse
translation/restriction comparison over `R` is the scalar restriction of the
one over `S`. Its proof evaluates on etale objects, expands the comparison for
composition of site maps, uses `restrictionCongr_inv_component` for the supplied
scheme-morphism equality, and uses preservation of composition.

Consequently `scalarRestriction_pullback_act` identifies the structure maps
in the two orders of equivariant pullback and scalar restriction.
`scalarRestrictionPullbackObjIso` is the identity on their common underlying
sheaf, with equivariance proved by this equality. These isomorphisms are natural
in coefficients and form `scalarRestrictionEquivariantPullbackIso`:

```
scalarRestrictionFunctor φ ρ ⋙ equivariantPullback R ρ τ f hf
  ≅ equivariantPullback S ρ τ f hf ⋙ scalarRestrictionFunctor φ τ.
```

Naturality reduces to the equality of the underlying restricted sheaf maps,
with identity morphisms on either side.

## Ordinary global sections and their group actions

Write `Γ_R` and `Γ_S` for the existing ordinary global-section functors.
`scalarRestrictionSectionsIso` is a natural isomorphism

```
sheafRestrictScalars φ X ⋙ Γ_R ≅ Γ_S ⋙ ModuleCat.restrictScalars φ.
```

The implementation uses the Library's canonical `sectionsIso`, which identifies
global sections with evaluation at the terminal object of the small-etale site.
Evaluation commutes with postcomposition by module scalar restriction. The
comparison is constructed by going from `R`-global sections to that evaluation
and then through the inverse `S`-comparison with scalars restricted.

`scalarRestriction_sectionsMap` proves that this comparison respects ordinary
geometric restriction along each etale `f`. More explicitly, first restricting
a section over `R` and then applying the comparison over `Y` gives the same map
as first applying the comparison over `X` and then scalar-restricting the
`S`-section restriction. The proof expands the section maps and comparison,
cancels the section isomorphisms, and identifies the same presheaf restriction
map evaluated at the terminal object.

For equivariant coefficients, the existing `pullbackSectionsFunctor` gives the
action of `g` by geometric restriction along `aut ρ g`, followed by the global
sections of `F.act g`. The theorem `scalarRestriction_sectionsAction` proves
that `scalarRestrictionSectionsIso` intertwines these actions. It combines the
geometric-restriction equation just described with naturality of the scalar
comparison at `F.act g`.

`scalarRestrictionSectionsFunctorIso` therefore constructs a natural
isomorphism with values in `Action (ModuleCat R) G`:

```
scalarRestrictionFunctor φ ρ ⋙ pullbackSectionsFunctor R ρ
  ≅ pullbackSectionsFunctor S ρ ⋙ (ModuleCat.restrictScalars φ).mapAction G.
```

The underlying isomorphism at `F` is `scalarRestrictionSectionsIso` at `F.obj`.
Naturality in equivariant coefficient morphisms is the ordinary section
comparison's naturality on their underlying sheaf maps.

## Remaining boundaries

This unit constructs scalar restriction, not tensor extension of scalars or
reduction modulo an ideal. It does not assert preservation of injectives or a
comparison in every derived cohomology degree. It does not construct specified
Harris coefficient sheaves, stable lattices, Shimura spaces, analytic sites,
compactly supported cohomology or continuous or smooth group actions. Those
remain separate constructions and theorem obligations. No additional coherence
for composition of ring homomorphisms is asserted here.
