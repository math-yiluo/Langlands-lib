# Reductions for restriction of rational characters to a split component

Author: Worker 33 (Task 3798, `6d0882ee-6e45-410c-b5a1-86d4544a4ffb`).

This module defines three conditional theorems and imports the shared central
split-torus reduction from
[CentralSplitTorusCharacterReduction](CentralSplitTorusCharacterReduction.md).
Together they provide four conditional theorems in the namespace
`Langlands.GroupScheme`. Each takes one Library proposition as a hypothesis, at
the same universe `u`, and uses only published Library results. The
unconditional theorem `characterRestriction` in
[`CharacterRestrictionProof`](CharacterRestrictionProof.md) applies the last
one to the published `reductiveCentralTorusSurjectivity`.

## The theorems

- `centralTorusCharacter_of_centralDerivedProduct`:
  `ReductiveCentralDerivedProductStatement.{u} → CentralTorusCharacterStatement.{u}`.
  For a connected reductive `G`, the hypothesis gives a commutative group
  scheme `Z` with affine, locally finite type structure morphism, a torus,
  a closed central subgroup inclusion `i : Z.toGrp ⟶ G`, and an actual
  derived subgroup `d : D ⟶ G` such that `subgroupProductMap i d` is an
  epimorphism. The published
  `IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`
  then shows that every nonzero rational character `χ` of `G` restricts to a
  nonzero character along `i`. The torus conjuncts are passed on unchanged.
- `centralSplitTorusCharacter_of_centralTorusCharacter`:
  `CentralTorusCharacterStatement.{u} → CentralSplitTorusCharacterStatement.{u}`.
  For a nonzero `χ`, the hypothesis gives a central torus `i : Z.toGrp ⟶ G`,
  affine and locally of finite type, with `characterRestrict i χ ≠ 0`. The
  published `CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus`
  gives `φ : 𝔾_m ⟶ Z` with `characterRestrict φ (characterRestrict i χ) ≠ 0`.
  `𝔾_m` is a split torus (`isSplitTorus_gm`), and `G` is affine
  (`hG.isAffineHom`), so the published `IsSplitTorus.exists_factor_isSplitSubtorus`
  factors `φ ≫ i` as `π ≫ j` with `j : A.toGrp ⟶ G` a split subtorus; `j` is
  central because `φ ≫ i` is (`IsCentral.comp`). If `characterRestrict j χ`
  were zero, then
  `characterRestrict (φ ≫ i) χ = characterRestrict π (characterRestrict j χ)`
  would be zero by `characterRestrict_comp`, a contradiction.
- `characterRestriction_of_centralSplitTorusCharacter`:
  `CentralSplitTorusCharacterStatement.{u} → CharacterRestrictionStatement.{u}`.
  For a split component `i` of a connected reductive `G`, injectivity of
  `characterRestrict i` is the published
  `characterRestrict_injective_of_centralSplitTorusCharacter`, and finite
  index of its range is the published, unconditional
  `IsSplitComponent.finiteIndex_range_characterRestrict`.
- `characterRestriction_of_torusSurjectivity`:
  `ReductiveCentralTorusSurjectivityStatement.{u} → CharacterRestrictionStatement.{u}`.
  It composes the three theorems above with the published
  `reductiveCentralDerivedProduct_of_torusSurjectivity`, which turns
  topological surjectivity of the product map into the epimorphism used by the
  first theorem.

## Provenance

Internal assembly of published Library results. The mathematical route (a
nonzero rational character is nonzero on a central torus, and then on a split
subtorus of it) follows J. S. Milne, *Algebraic Groups* (2017), Proposition
21.61 and Exercises 12-5 and 12-6, and Renard, *Représentations des groupes
réductifs p-adiques*, V.2.6.
