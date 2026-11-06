# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_reactivate "N₁ N₂ …"` (from `P2M.Util`; it re-activates the scoped declarations of the namespaces) is replaced by `open scoped N₁ N₂ …`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `C10QuotAdic`). The quotient system is `Q k := idealPowQuot q 𝓙 (F k) 0`, the presheaf
`F k / 𝓙 F k` of the Library module `Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration`.
`eps F : AffHom F (idealPowQuot q 𝓙 F 0)` is the quotient map (through `toPow0`, the identification of `F` with
`𝓙⁰ F`); it is surjective with kernel `idealPowSub q 𝓙 F 1` on affines (`eps_surjective`, `ker_eps_app`).
An affine-indexed map `φ` preserves the submodules `𝓙^k F(U)` (`map_mem_idealPowSub`), and onto them when
surjective (`exists_mem_idealPowSub_map_eq`), so it induces `tau φ` on the quotients (`tauTop`, `tau`), with
`tau φ ∘ eps = eps ∘ φ` (`tau_comp_eps`), surjective when `φ` is (`tau_surjective`), and with kernel
`I' • ⊤` when `ker φ = I' • ⊤` and `φ` is surjective (`ker_tau_app`). `solution` takes `Q`, `τ := tau (φ k)`,
`ε := eps (F k)`, and uses the Library facts that the quotients are coherent and quasi-coherent
(`isCoherent_idealPowQuot`, `isQuasicoherent_idealPowQuot`, `P` locally noetherian) and annihilated by `𝓙`
(`idealAnnihilates_idealPowQuot`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.toPow0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.toPow0_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.toPow0_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.eps`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.eps_app_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.map_mem_idealPowSub`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.exists_mem_idealPowSub_map_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.tauTop`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.tauTop_coe`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.tau`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.tau_app_mkQ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.ker_eps_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.eps_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.tau_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.tau_comp_eps`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.C10QuotAdic.ker_tau_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot` (Library).
Other imports: `Mathlib`.
