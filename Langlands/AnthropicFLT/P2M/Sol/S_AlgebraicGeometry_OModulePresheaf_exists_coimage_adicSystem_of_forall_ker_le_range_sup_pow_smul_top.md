# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top`.

Proof (namespace `CoimageAdic29` for helpers). A linear map whose kernel contains that of a surjection `f` descends
along `f` (`descend`, `descend_apply`), also for affine homomorphisms (`descendAff`, `descendAff_app`,
`descendAff_comp`, with `range_descendAff` and `ker_descendAff` = image of the kernel); surjective maps carry
`J • ⊤` onto `J • ⊤` (`map_smul_top_of_surjective`).

`solution`: for each `k`, the ported theorem `AffHom.exists_isQuasicoherent_surjective_ker_eq_range` gives the
cokernel `ε k : F k → E k` of `j k` (coherent, quasi-coherent, surjective on affines, kernel `range (j k)`). The maps
`ε k ∘ φ k` kill `ker ε (k+1) = range j (k+1)` (by `hjc`), so they descend to `τ k : E (k+1) → E k`, surjective;
its kernel is the image of `ker φ k + range j (k+1)`, i.e. `I^(k+1) • ⊤` (using `κ` surjective to lift elements of
`range j k`). Likewise `u k` kills `range j k` and descends to `uE k : E k → Ps k`, compatible with `π` and `τ`, with
the same range as `u k`. Finally `hAR` (kernel of `u` inside `range j + I^(k+1) F`) becomes
`ker (uE (k+c)) ⊆ I^(k+1) E (k+c)` after applying `ε`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.descend`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.descend_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.descendAff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.descendAff_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.descendAff_comp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.range_descendAff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.ker_descendAff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.CoimageAdic29.map_smul_top_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range` (same contribution).
Other imports: `Mathlib`.
