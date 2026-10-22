# Actions on derived functors from structure maps into translates

Author: Worker 13. Companion of Worker 13's `Langlands.Cohomology.TranslationAction`,
whose translation data `Data Γ T` and helper lemmas it reuses, in the same
namespace.

The setting is that of `TranslationAction`. `C` and `D` are abelian,
`Γ : C ⥤ D` is additive, `G` is a monoid, and the functors `T g` are additive,
preserve homology and preserve injective objects. `𝒯 : Data Γ T` supplies
`sections`, `comp` and `one` with their coherences.

## Coequivariant objects

`Coequivariant 𝒯` consists of an object `obj` with structure maps
`coact g : obj ⟶ (T g).obj obj` into the translates, satisfying
`coact 1 = one.inv` and
`coact (g * h) = coact g ≫ T g (coact h) ≫ (comp g h).hom`.
These are the maps that arise for constant sheaves, whose maps out are
determined by an adjunction.

## Chain maps and homotopies

Fix an injective resolution `I` of `F.obj`.

- `colift F g I` is Mathlib's `InjectiveResolution.desc` of `F.coact g`, from
  `I` to the mapped resolution `T g I`. `colift_comm` and `colift_comm_zero`
  record its lifting property.
- `cochainMap Γ F g I` is `Γ` of `colift F g I`, followed termwise by
  `sections g`.
- `compositeColift F g h I` is the lift of `g`, then `T g` of the lift of `h`,
  then `comp g h`. `compositeColift_comm` proves that it lifts
  `coact (g * h)`.
- `comulHomotopy` is a homotopy from `cochainMap g ≫ cochainMap h` to
  `cochainMap (g * h)`. Naturality of `sections g` and `sections_comp` give an
  equality with `Γ` of `compositeColift` followed by `sections (g * h)`. Two
  lifts of the same map are homotopic (`InjectiveResolution.descHomotopy`).
- `oneColift_comm` and `coOneHomotopy` give a homotopy from `cochainMap 1`
  to the identity, using `sections_one` and `coact_one`.

## Actions

- Composition of the induced maps on homology is reversed. Hence
  `coHomologyAction Γ F I n : Gᵐᵒᵖ →* End (H^n(Γ(I)))` sends `op g` to the
  homology map of `cochainMap g`.
- For a group `G`, `coCohomologyAction Γ F I n : Action D G` is the degree `n`
  homology of `Γ(I)`. Here `g` acts through `op g⁻¹`, using Mathlib's
  `MulEquiv.inv'`.

## Provenance and scope

This is derived infrastructure, like `TranslationAction`. Harris, *Galois
properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ.
39-2 (1999), Theorem 5.7, printed p.313, uses Galois actions on étale
cohomology with coefficients. Worker 13 read this passage in the original. Not
treated here: independence of the resolution as an isomorphism of actions,
functoriality in morphisms, and any topology on `G`.

Source registration:
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Project imports outside this submission are present in Library commit
`0686b4fa6c8df22845bba2e2668a723a41d47c84`.
