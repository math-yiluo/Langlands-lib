# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `P2mStableKerSol`). Section `Generic` repeats three elementary facts on `J • ⊤` under linear
maps. Structure `Sys` bundles the data `F`, `Ps`, `φ`, `π`, `u` and their hypotheses. The subsystem is the
"stable kernel": `Khat U` is the submodule of sequences `s m ∈ F m (U)` that are compatible under the `φ m`
and killed by the `u m` on every affine `W ≤ U` (the inverse limit of the kernels), and `SMod n U` is its
projection to `F n (U)`. `St n` is the presheaf `U ↦ SMod n U` with inclusion `ι n : AffHom (St n) (F n)`
(injective, range `SMod n`) and transition maps `lam n` induced by `φ n` (surjective, since the projections
are compatible, `map_φ_SMod`); `u n ∘ ι n = 0` (`u_comp_ι`). `St n` is coherent as a submodule of a finite
module over the noetherian ring of sections of an affine open (`isCoherent_St`, `P` locally noetherian
because `q` is locally of finite type over noetherian `A`).

Artin–Rees on an affine `U` (`AR`, `exists_AR`): over the noetherian ring `Γ(P, U)` with the extended ideal
`J`, the ported theorem
`Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`
applied to the section maps (`appSections`) and the inverse limit `KB U` of the kernels gives `c` with
`ker (u n) ≤ SMod n ⊔ I^(k+1) • ⊤` and `I^n • ⊤ ⊓ SMod n ≤ I^k • SMod n` for `k + c ≤ n` (restriction of
scalars from `Γ(P, U)` to `A` translates the powers of `J` into powers of `I`). Quasi-coherence of `St n`
(`isQuasicoherent_St`) uses this bound: an element of `SMod n (D(f))` is the image of a compatible kernel
sequence on `D(f)`; its component at level `n + c` extends, after multiplication by a power of `f`, to a
kernel element over `U` (`exists_ker_ext`, quasi-coherence of `F` and `Ps`), which by the bound lies in
`SMod (n+c) ⊔ I^(n+1) • ⊤` and maps down to an element of `SMod n U` with the right restriction
(`push_down`). When every `u n` is surjective on affines, kernel elements lift step by step
(`ker_step`, `seq0`, `seqMod`, `exists_family`), so `SMod n U = ker (u n)` (`SMod_eq_ker`).
`solution` assembles `St`, `ι`, `lam` and these facts.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.map_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.map_smul_top_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.pow_smul_top_eq_bot`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.huc_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.pow_smul_top_F`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.Khat`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.mem_Khat`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.Khat_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.Khat_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.compat_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.ker_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.mem_Khat_of_compat`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.SMod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.mem_SMod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.SMod_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.SMod_res`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.sModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.St`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.St_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.St_res_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.St_smul_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.ι`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.ι_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.ι_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.range_ι`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.φ_mem_SMod`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.lam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.lam_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.ι_lam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.lam_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.u_comp_ι`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.SMod_le_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.map_φ_SMod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.isCoherent_St`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.exists_ker_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.push_down`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.isQuasicoherent_St`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.KB`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.mem_KB_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.restrictScalars_map_KB`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.AR`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.exists_AR`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.ker_step`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.KerT`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.seq0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.seq0_succ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.seqMod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.seqMod_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.seqMod_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.seqMod_at`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.exists_family`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.P2mStableKerSol.Sys.SMod_eq_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
