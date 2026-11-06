# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le`.

Proof (namespace `AdicEnvelopeSol`). Section `Generic`: images of `J • ⊤` under linear maps
(`map_mem_smul_top`, `map_smul_top_of_surjective`) and `pow_smul_top_eq_bot` (a module that is the quotient
of another by `J • ⊤` is killed by `J`). Section `Trunc`: for an FLT presheaf `E`, `trunc I E k` is the
presheaf `U ↦ E(U) ⧸ I^(k+1) • ⊤` with quotient map `truncπ` and transition maps `truncτ`
(`trunc I E (k+1) → trunc I E k`), both surjective on affines with kernels `I^(k+1) • ⊤`; `trunc` preserves
coherence and quasi-coherence (`isCoherent_trunc`, `isQuasicoherent_trunc`).

Structure `Sys` bundles the data of the theorem (`G := F`, `L`, `γ := φ`, `ι`, `lam` and the hypotheses on
them), and `AR U c` is the Artin–Rees type hypothesis `hAR` on the affine `U` with constant `c`. With
`Q n k := trunc I (L n) k`, `lam` induces maps `t n k : Q (n+1) k → Q n k` (surjective; injective on `U`
once `k + c ≤ n`, by `ker_lam_le`, which uses `AR U c` and injectivity of `ι`). `K k` is the presheaf of
families `x n ∈ Q n k (U)` compatible under the `t n k` on every affine `W ≤ U` (`Kmod`, `K`): the inverse
limit over `n` of `L n / I^(k+1) L n`. On an affine `U` the evaluation `ev n k : K k (U) → Q n k (U)` is
surjective (`ev_surjective'`, by recursively lifting through the surjective `t`, `seqMod`) and injective
for `k + c ≤ n` (`ev_injective`), so the limit stabilises. The truncation maps `r n k` induce
`κ k : K (k+1) → K k`, surjective with kernel `I^(k+1) • ⊤` on affines (`κ_surjective`, `ker_κ`), and
`j k : K k → F k` sends `x` to `ι k (x k)` (well defined since `I^(k+1)` kills `F k` on affines,
`T_le_ker_ι`); `range_j` (range of `j k` is the range of `ι k`) and `j_comp_κ` (compatibility with `φ`)
follow. `K k` is coherent and quasi-coherent since it agrees with a single `Q n k` through `ev` on affines
(`isCoherent_K`, `isQuasicoherent_K`). Finally `ker_j_le`: an element of `K n (U)` killed by `j n` has
components in `I^(k+1) • ⊤` for `k + c ≤ n` (`ker_t_le`, `apply_mem_pow_smul_top_of_apply_eq_zero`).
`solution` builds `S`, takes `Ks := S.K`, `κ := S.κ`, `j := S.j`, and assembles these facts.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.map_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.map_smul_top_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.pow_smul_top_eq_bot`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.T`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.T_def`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.T_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.T_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.T_anti`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.truncModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.trunc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.trunc_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.trunc_res_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.trunc_smul_mk`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.truncπ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.truncπ_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.truncπ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.ker_truncπ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.truncτ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.truncτ_app_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.truncτ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.ker_truncτ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.isCoherent_trunc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.isQuasicoherent_trunc`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ι_lam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.lam_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.pow_smul_top_G`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.AR`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ker_lam_le`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.Q`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.t`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.t_mk`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.r`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.t_r_comm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.t_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.t_injective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.Kmod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.mem_Kmod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.Kmod_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.Kmod_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.compat_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.mem_Kmod_of_compat`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.piRes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.piRes_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.kModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.K_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.K_res_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.K_smul_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ev`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ev_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.seq0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.seqMod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.seqMod_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.seqMod_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.seqMod_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.seqMod_at`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ev_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ev_surjective'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ev_injective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.piRed`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.piRed_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.κ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.κ_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.T_le_ker_ι`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.e`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.e_mk`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.j`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.j_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.range_j`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.j_comp_κ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.κ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ker_κ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.isCoherent_K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.isQuasicoherent_K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ker_t_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.apply_mem_pow_smul_top_of_apply_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.AdicEnvelopeSol.Sys.ker_j_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
