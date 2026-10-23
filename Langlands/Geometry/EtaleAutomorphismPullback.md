# Automorphism translation and étale pullback

This module compares the published automorphism-translation action with the
published geometric pullback maps on ordinary small-étale cohomology. It
constructs the action on the right-derived global-section module itself and
an equivariant isomorphism from the existing resolution-based action.

## Parameters and conventions

Let `Y : Scheme.{u}`, let `R : Type u` be a commutative ring, and let
`G : Type w` be a group with a homomorphism `ρ : G →* (Aut Y)ᵐᵒᵖ`.
Write `σ_g = EtaleCohomologyAction.aut ρ g`. The existing convention is
`σ_(g*h) = σ_g ≪≫ σ_h`, giving a left action on cohomology.

Coefficients are actual sheaves of `ModuleCat.{u} R` on `Y.smallEtaleTopology`.
An `EquivariantSheaf R ρ` consists of such a sheaf `F.obj` with maps
`F.act g : (translateBy R ρ g).obj F.obj ⟶ F.obj` satisfying the published
unit and product laws. The degree `q` is any natural number. No topology on
`G`, smoothness, or continuity hypothesis is imposed or concluded.

## Restriction and sections

For any category `A` and automorphism `σ : Y ≅ Y`,
`EtalePullback.restrictionAutomorphismIso` identifies
`restriction σ.hom A` with `EtaleAutomorphism.translate A σ`. These two
functors are definitionally equal, so the comparison is `Iso.refl`.

`terminalSectionsMap_automorphism` proves that the terminal-object section
map of restriction equals the inverse of the existing translation section
comparison. Unfolding both constructions reduces this to equality of the
arrows to the terminal étale object.

For module coefficients, let `Γ = EtaleDerivedSections.sections Y R`,
let `Γt = EtaleCohomologyAction.sectionsTop R`, and let
`ε : Γ ≅ Γt` be `EtaleDerivedSections.sectionsIso Y R`.
`sectionsMap_automorphism` states the formula

```text
sectionsMap(σ).app F = ε.hom.app F ≫ sectionsIso(σ).inv.app F
  ≫ ε.inv.app (restriction(σ).obj F).
```

Here `sectionsIso(σ)` denotes `EtaleAutomorphism.sectionsIso (ModuleCat R) σ`.

## Comparison on resolutions

Fix an equivariant sheaf `F`, a group element `g`, and any injective resolution
`I` of `F.obj`. Write `ℓ_g = TranslationAction.lift F g I`.
`pullbackActionChainMap R ρ F g I` is the endomorphism `B_g` of `Γ(I)`
obtained by composing `resolutionSectionsMap σ_g.hom R I` with `Γ(ℓ_g)`.
The source of `ℓ_g` is definitionally the cocomplex of the restricted
resolution, so this is an actual composition of chain maps.

Let `A_g = TranslationAction.chainMap Γt F g I` and
`η = NatIso.mapHomologicalComplex ε (ComplexShape.up ℕ)`.
`pullbackActionChainMap_comm` proves

```text
A_g ≫ η.inv.app I.cocomplex = η.inv.app I.cocomplex ≫ B_g.
```

Its proof is degreewise: the section formula cancels the adjacent comparison
maps, and naturality of `ε.inv` at each component of `ℓ_g` gives the equality.

Let `H_q` be the homology functor on cochain complexes of modules, and let
`e = I.isoRightDerivedObj Γ q`. The theorem
`pullbackActionChainMap_cohomology` proves

```text
cohomologyMapWithCoefficients σ_g.hom R q (F.act g)
  = e.hom ≫ H_q.map B_g ≫ e.inv.
```

It applies the published `cohomologyMapWithCoefficients_ofResolutions` to
`ℓ_g`. The required degree-zero augmentation equality is precisely
`TranslationAction.lift_comm_zero`, after the formula for the augmentation
of a mapped injective resolution.

## The cohomology action and its comparison

For the chosen resolution `I = injectiveResolution F.obj`, put
`c = EtaleCohomologyAction.cohomologyIso R ρ F q`. Its source is the module
underlying the existing translation action, and its target is
`(EtaleDerivedSections.cohomology Y R q).obj F.obj`.
The theorem `cohomologyIso_comm` proves

```text
TranslationAction.homologyAction Γt F I q g ≫ c.hom
  = c.hom ≫ cohomologyMapWithCoefficients σ_g.hom R q (F.act g).
```

The proof applies `H_q` to the chain comparison above, substitutes the
resolution formula, and cancels `e.inv ≫ e.hom`.

`pullbackCohomologyAction R ρ F q` has the published right-derived cohomology
module as its underlying object. Its monoid homomorphism is obtained by
conjugating the existing homology action by `c`; hence its unit and
multiplication laws follow from those of that action and of conjugation.
`pullbackCohomologyAction_ρ` then proves that its value at every `g` is exactly
`cohomologyMapWithCoefficients σ_g.hom R q (F.act g)`.
Finally, `pullbackCohomologyActionIso` upgrades `c` to an isomorphism in
`Action (ModuleCat R) G`, using the proved intertwining equality.

## Provenance and remaining specialization

This is an internal comparison and construction from the actual published
`EtaleCohomologyAction`, `TranslationAction`, and
`EtaleDerivedPullbackFunctoriality` APIs. It asserts no new original-literature
theorem. The comparison is proved from their section formulas, resolution
lifts and homology functoriality; no cohomology comparison is assumed as data.

This unit concerns ordinary small-étale cohomology of a supplied actual scheme
and supplied equivariant sheaf. It does not construct a Shimura scheme or
coefficient system, identify the action with a varying-scheme diagram, or
assert compact support, a Galois realization, smoothness, scalar change, or
inverse-limit compatibility. Those geometric and analytic specializations
remain obligations of the broader framework.
