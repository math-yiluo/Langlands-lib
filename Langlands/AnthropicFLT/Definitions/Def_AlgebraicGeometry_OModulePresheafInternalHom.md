# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_OModulePresheafInternalHom.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Let `R` be a commutative ring, `π : V ⟶ Spec R` and `F`, `G` FLT presheaves of modules over `π`.
`OModulePresheaf.internalHom F G` is an FLT presheaf of modules over `π`, a model of the internal Hom
`Hom(F, G)` that only uses affine opens:

- `AffBelow U` is the type of affine opens `W ≤ U`, and `HomPi F G U` the `R`-module of families of `R`-linear
  maps `F(W) → G(W)` indexed by them.
- `homSub F G U` is the `R`-submodule of families that are `Γ(V, W)`-linear on each `W` and commute with the
  restrictions between affine opens `W ≤ W'` below `U` (`mem_homSub_iff`); these are the sections of
  `internalHom F G` over `U` (`internalHom_obj`).
- `Γ(V, U)` acts by restricting the scalar to each `W` (`sectionsSMul`, `smulSections`,
  `moduleSectionsHomSub`; `smul_comm_sections` is the commutation of the `R`- and `Γ(V, W)`-actions used
  here), and the restriction maps `homRes` restrict the index set.
- `internalHom.eval W hW` evaluates a section over `U` at an affine `W ≤ U`; `internalHom.toAffHom` and
  `internalHom.ofAffHom` are mutually inverse identifications of global sections (over `⊤`) with affine-indexed
  homomorphisms `AffHom F G` (`toAffHom_ofAffHom`, `ofAffHom_toAffHom`).

The other declarations are unfolding lemmas: `sectionsSMul_apply`, `sections_smul_apply`, `homRes_apply`,
`internalHom_res_apply`, `internalHom_smul_apply`, `eval_apply`.

## Declarations

Names, namespaces and statements are the FLT ones.

- abbrev `AlgebraicGeometry.OModulePresheaf.AffBelow`
- abbrev `AlgebraicGeometry.OModulePresheaf.HomPi`
- def `AlgebraicGeometry.OModulePresheaf.homSub`
- theorem `AlgebraicGeometry.OModulePresheaf.mem_homSub_iff`
- theorem `AlgebraicGeometry.OModulePresheaf.smul_comm_sections`
- def `AlgebraicGeometry.OModulePresheaf.sectionsSMul`
- theorem `AlgebraicGeometry.OModulePresheaf.sectionsSMul_apply`
- instance `AlgebraicGeometry.OModulePresheaf.smulSections`
- theorem `AlgebraicGeometry.OModulePresheaf.sections_smul_apply`
- instance `AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub`
- def `AlgebraicGeometry.OModulePresheaf.homRes`
- theorem `AlgebraicGeometry.OModulePresheaf.homRes_apply`
- def `AlgebraicGeometry.OModulePresheaf.internalHom`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom_obj`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom_res_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom_smul_apply`
- def `AlgebraicGeometry.OModulePresheaf.internalHom.eval`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom.eval_apply`
- def `AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom`
- def `AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_ofAffHom`
- theorem `AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_toAffHom`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
