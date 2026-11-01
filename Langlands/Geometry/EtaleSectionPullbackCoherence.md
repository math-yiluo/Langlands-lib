# Identity and composition for actual geometric section pullback

This module constructs successive ordinary geometric section pullback and proves
that the existing actual section maps respect identity and composition. All
comparisons use the constructed small-etale inverse/direct images and their
adjunctions.

## Parameters and scope

Let `X`, `Z`, and `V` be schemes in `Scheme.{u}`, let `f : Z ⟶ X` and
`g : V ⟶ Z` be arbitrary morphisms, and let `R : Type u` be a commutative ring.
The coefficient category is `ModuleCat.{u} R`. Write

- `L_f = EtaleInverseImage.inverseImage f R`;
- `D_f = EtaleDirectImage.directImage f (ModuleCat.{u} R)`;
- `Γ_X = EtaleDerivedSections.sections X R`;
- `s_f = EtaleDerivedGlobalPullback.sectionsPullback f R`.

Thus the sheaves are actual module-valued sheaves on the small-etale site,
and `s_f : Γ_X ⟶ L_f ⋙ Γ_Z` is the published map obtained from the
inverse/direct adjunction unit and the preserved-terminal section comparison.
No etaleness, flatness, affineness, finiteness, or Noetherian premise on `f` or
`g` is imposed. The declarations require no chosen derived categories or
localization universes, despite importing the existing normalization module.

## Coherence of the direct-image section comparisons

Write `S_f : D_f ⋙ Γ_X ≅ Γ_Z` for
`EtaleDerivedDirectImage.directImageSectionsIso f R`.

`terminalSectionsIso_id` and `terminalSectionsIso_comp` prove the corresponding
identities first for evaluation at the terminal small-etale object. The
comparison maps in the presheaf arguments have terminal targets: base change
preserves terminal objects. Uniqueness of a map into those terminal objects
therefore identifies the maps, and applying the original coefficient presheaf
gives the asserted equalities.

`directImageSectionsIso_id` states, for every sheaf `F` on `X`,

```text
S_id.hom.app F = Γ_X.map (directImageId.hom.app F).
```

`directImageSectionsIso_comp` states, for every sheaf `F` on `V`,

```text
S_f.hom.app (D_g.obj F) ≫ S_g.hom.app F
  = Γ_X.map (directImageComp.hom.app F) ≫ S_(g≫f).hom.app F.
```

The identity and composition isomorphisms on the right are the existing
geometric direct-image comparisons from `EtaleImageFunctoriality`. The proofs
transport the terminal-evaluation identities through `sectionsIso`; naturality
of this existing isomorphism supplies the required ordinary-section maps.

## Coherence of ordinary section pullback

The existing `inverseImageId R X` has direction `L_id ≅ 𝟭`, and the existing
`inverseImageComp R f g` has direction `L_f ⋙ L_g ≅ L_(g≫f)`.

`inverseImageIdentity_unit` proves that the ordinary identity-adjunction unit,
followed by the actual direct-image identity comparison, equals
`inverseImageId.inv.app F`. The proof uses `unit_conjugateEquiv` and the
published `conjugate_inverseImageId`, then naturality of `directImageId`.
Consequently `sectionsPullback_id` proves

```text
s_id.app F ≫ Γ_X.map (inverseImageId.hom.app F) = 𝟙 (Γ_X.obj F).
```

`inverseImageComposition_unit` expresses the actual unit for `g ≫ f` as the
unit for `f`, then `D_f` of the unit for `g`, then the successive direct images
of the inverse-image composition map, and finally the geometric direct-image
composition map. It follows from `unit_conjugateEquiv`, the published
`conjugate_inverseImageComp`, and the formula for the composite adjunction unit.

`sectionsPullback_comp` proves, for every sheaf `F` on `X`,

```text
s_f.app F ≫ s_g.app (L_f.obj F)
  ≫ Γ_V.map (inverseImageComp.hom.app F)
  = s_(g≫f).app F.
```

The proof moves the unit for `g` and the coefficient composition map through
`S_f` and `S_g` by their naturality. The direct-image section composition law
then reduces the calculation to `inverseImageComposition_unit`. The coefficient
comparison is thus the existing one determined by the actual adjunctions.
Neither it nor the asserted equality is an input.

`compositeSectionsPullback R f g` constructs the natural transformation

```text
Γ_X ⟶ (L_f ⋙ L_g) ⋙ Γ_V
```

by successive `s_f` and `L_f` whiskering of `s_g`, with the actual functor
associator. `compositeSectionsPullback_eq` identifies its composite with
`inverseImageComp.hom` whiskered by `Γ_V` with the existing `s_(g≫f)`.
This is an equality of natural transformations in the coefficient sheaf.

## Provenance and remaining obligations

This is an internal construction and coherence calculation from the published
`EtaleDerivedGlobalNormalization`, `EtaleDerivedDirectImage`,
`EtaleImageFunctoriality`, and `EtaleInverseImageCoherence` implementations.
The categorical ingredients are the original terminal-preservation and
adjunction-mate constructions in pinned Mathlib, specifically
`CategoryTheory/Limits/Preserves/Shapes/Terminal.lean` (`PreservesTerminal.iso`
and `isLimitOfHasTerminalOfPreservesLimit`) and
`CategoryTheory/Adjunction/Mates.lean` (`unit_conjugateEquiv`), together with
`Adjunction.comp_unit_app` in `CategoryTheory/Adjunction/Basic.lean`.
The arguments above describe the implemented Lean proofs.

This module proves the ordinary global-section laws. Their transport to
bounded-below complexes and the existing derived and higher-cohomology maps
remains separate work. Agreement with the older etale-restriction model,
coefficient-ring coherence, compact supports, smooth actions, and Harris
specialization also remain separate obligations.
