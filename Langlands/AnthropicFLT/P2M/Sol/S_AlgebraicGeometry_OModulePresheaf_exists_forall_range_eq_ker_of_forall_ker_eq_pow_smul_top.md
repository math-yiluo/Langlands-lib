# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `P2mAdicKerSol`): the kernels of a surjection of adic systems form an adic system, built as the
inverse limit of the truncated kernels.

- Generic lemmas on `J • ⊤` (`map_mem_smul_top`, `map_smul_top_of_surjective`, `pow_smul_top_eq_bot`).
- Truncation: for a presheaf `E`, `trunc I E k` is the presheaf `U ↦ E(U) / I^(k+1) E(U)` (`T`, `T_def`,
  `T_smul_mem`, `T_res`, `T_anti`, `truncModuleSections`, `trunc_obj`, `trunc_res_mk`, `trunc_smul_mk`), with the
  projection `truncπ` and transition maps `truncτ`, surjective with kernels `I^(k+1) • ⊤` (`truncπ_app`,
  `truncπ_surjective`, `ker_truncπ`, `truncτ_app_mk`, `truncτ_surjective`, `ker_truncτ`); it is coherent or
  quasi-coherent with `E` (`isCoherent_trunc`, `isQuasicoherent_trunc`).
- `Sys` bundles the data together with kernels `ι n : L n → G n` of the `θ n`. The image of
  `γ n ∘ ι (n+1)` lies in the image of `ι n` (`ι_mem_ker`, `γι_mem_range`), giving `lam n : L (n+1) → L n`
  (`lamApp`, `ι_lamApp`, `ι_lam`), surjective since `I^(n+1)` kills `G n` (`pow_smul_top_G`, `lam_surjective`).
- Artin–Rees: `AR U c` says `I^n G_n ∩ ker θ_n ⊆ I^k ker θ_n` for `k + c ≤ n` on `U`; on a noetherian affine with
  `G 0(U)` finite it holds for some `c` (`exists_AR`, from the ported theorem
  `Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top` over `Γ(P, U)` with
  `J = I Γ(P, U)`). Then `ker (lam n) ⊆ I^(k+1) L(n+1)` for `k + c ≤ n` (`ker_lam_le`).
- `Q n k = trunc I (L n) k` with maps `t n k` induced by `lam` and `r n k` the truncation maps, which commute
  (`t_mk`, `t_r_comm`); `t n k` is surjective and, under `AR U c` with `k + c ≤ n`, injective (`t_surjective`,
  `t_injective`). `K k` is the presheaf of compatible sequences `(x n) ∈ ∏_n Q n k` (`Kmod`, `mem_Kmod`,
  `Kmod_smul_mem`, `Kmod_res`, `compat_of_mem`, `mem_Kmod_of_compat`, `piRes`, `piRes_apply`, `kModuleSections`,
  `K_obj`, `K_res_val`, `K_smul_val`), with evaluations `ev n k` (`ev_apply`). Evaluation is surjective by
  extending sequences (`seq0`, `seqMod`, `seqMod_zero`, `seqMod_succ`, `seqMod_of_le`, `seqMod_at`,
  `ev_surjective`, `ev_surjective'`) and injective for `k + c ≤ n` (`ev_injective`), so `K k(U) ≅ Q (k+c) k(U)`.
- Maps: `κ k : K (k+1) → K k` applies `r n k` componentwise (`piRed`, `piRed_mem`, `κ_val`), and
  `j k : K k → G k` is evaluation at `n = k` followed by `ι k` (well defined since `I^(k+1)` kills the image,
  `T_le_ker_ι`, `e`, `e_mk`, `j_app`), with image `ker θ k` (`range_j`) and `γ k ∘ j (k+1) = j k ∘ κ k`
  (`j_comp_κ`). Under Artin–Rees, `κ k` is surjective with kernel `I^(k+1) • ⊤` (`κ_surjective`, `ker_κ`), and
  each `K k` is coherent and quasi-coherent (`isCoherent_K`, `isQuasicoherent_K`).
- `main`: `P` is locally noetherian; the ported theorem `AffHom.exists_isQuasicoherent_injective_range_eq_ker` gives
  the kernels `L n` (coherent), Artin–Rees holds on every affine, and `K`, `κ`, `j` satisfy the claim.
  `solution` is `P2mAdicKerSol.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.map_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.map_smul_top_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.pow_smul_top_eq_bot`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.T`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.T_def`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.T_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.T_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.T_anti`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.truncModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.trunc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.trunc_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.trunc_res_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.trunc_smul_mk`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.truncπ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.truncπ_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.truncπ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.ker_truncπ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.truncτ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.truncτ_app_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.truncτ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.ker_truncτ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.isCoherent_trunc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.isQuasicoherent_trunc`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ι_mem_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.γι_mem_range`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.lamApp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ι_lamApp`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.lam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ι_lam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.pow_smul_top_G`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.lam_surjective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.AR`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.exists_AR`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ker_lam_le`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.Q`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.t`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.t_mk`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.r`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.t_r_comm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.t_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.t_injective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.Kmod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.mem_Kmod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.Kmod_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.Kmod_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.compat_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.mem_Kmod_of_compat`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.piRes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.piRes_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.kModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.K_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.K_res_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.K_smul_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ev`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ev_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.seq0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.seqMod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.seqMod_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.seqMod_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.seqMod_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.seqMod_at`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ev_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ev_surjective'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ev_injective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.piRed`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.piRed_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.κ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.κ_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.T_le_ker_ι`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.e`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.e_mk`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.j`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.j_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.range_j`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.j_comp_κ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.κ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.ker_κ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.isCoherent_K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.Sys.isQuasicoherent_K`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.P2mAdicKerSol.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker` (same contribution).
Other imports: `Mathlib`.
