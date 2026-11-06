# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- `p2m_export` also exports from namespaces that contain only private declarations of this module (`GEDriver`), which Lean does not register as namespaces; Lean's `export` rejects them, so each of them is registered by an empty block `namespace N end N` right after the options.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`.

Proof (namespace `GEDriver`): Grothendieck's existence theorem for proper `q`, by noetherian induction on the support
and Chow's lemma, following the dévissage of EGA III 5.1.4 / Stacks 088C.

- Helpers: vanishing ideals of closed sets have the right support, are radical, and cut out reduced, and for
  irreducible sets integral, closed subschemes (`support_vanishingIdeal`, `radical_vanishingIdeal`,
  `isReduced_subscheme_vanishingIdeal`, `irreducibleSpace_subscheme_vanishingIdeal`,
  `isIntegral_subscheme_vanishingIdeal`); `P` is compact and noetherian (`compactSpace_of_isProper`,
  `isNoetherian_of_isProper`, `noetherianSpace_of_isProper`); closed immersions and compositions are proper and
  separated (`isProper_subschemeι`, `isProper_comp`, `isSeparated_of_isProper`); `idealAnnihilates_ker_subschemeι`;
  ordered affine covers exist (`nonempty_orderedAffineCover_of_compactSpace_univ`); a reducible nonempty closed set
  is the union of two smaller closed sets (`exists_closeds_lt_sup_eq`); ideal products
  (`vanishingIdeal_sup_pow_mul_le`, `vanishingIdeal_top_ideal_le_radical_bot`).
- `AdicSys` bundles a coherent quasi-coherent adic system and `Algebraised` says it is the system `G / I^(k+1) G` of a
  coherent `G`; `KilledBy 𝓙 t` says that `𝓙^t` kills it (`killedBy_one_iff`, `idealOf T = vanishingIdeal T`).
  Trivial cases: zero systems, `t = 0`, and empty support (`algebraised_of_forall_eq_zero`,
  `algebraised_of_killedBy_zero`, `algebraised_of_killedBy_coe_eq_empty`).
- `algebraised_of_quot_of_ker` (dévissage): if every system killed by an ideal sheaf `𝓙` is algebraised and every
  system mapping injectively (up to Artin–Rees) onto the `𝓙`-part of `S` is algebraised, then `S` is algebraised.
  The `𝓙`-part `𝓙 • S` of `S` and the quotient system are built with the ported theorems
  `exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top` and
  `exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top`, and the extension is algebraised by
  the ported theorem
  `exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`.
- `stepC` (integral case): for `T` irreducible and `S` killed by `idealOf T`, the Library Chow lemma
  (`ChowDatum.nonempty`, `ChowDatumProj.nonempty_of`) applied to the integral closed subscheme `T` gives a scheme
  `V'`, projective over `A` through a closed immersion into some `ℙ^N_A`, with a proper map `p : V' → T` that is an
  isomorphism over a nonempty open. Pull `S` back to `V'` (ported theorem
  `exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom`, with an ordered
  affine cover of `V'` from the ported theorem `Scheme.nonempty_orderedAffineCover_of_compactSpace_univ`),
  algebraize there by the projective case (ported theorem
  `exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete`), and compare `S` with
  the Čech pushforward of the pullback (ported theorems `exists_affHom_cechPushforward_apply_eq_of_forall_res_eq`,
  `exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`). The kernel and cokernel of
  this comparison are killed by a power of the ideal of a closed set `T' < T` (ported theorems
  `exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty`,
  `exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper`,
  `forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top`); the kernel, image and cokernel systems
  (ported theorems `exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top`,
  `exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top`) are therefore algebraised by the induction
  hypothesis or as quotients of the algebraised pushforward (ported theorem
  `exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete`), and `S` is
  algebraised as an extension (ported theorem
  `exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`).
- `algebraised_of_killedBy`: well-founded induction on the closed set `T` (generalizing `t` and `S`). First the case
  `t = 1`: for `T` irreducible apply `stepC`; for `T` empty the system is zero; otherwise split `T = T₁ ∪ T₂` with
  `T₁, T₂ < T` (`exists_closeds_lt_sup_eq`) and use `algebraised_of_quot_of_ker` with `idealOf T₁`, the quotient
  systems being algebraised by the induction hypothesis for `T₁` and the `idealOf T₁`-parts by that for `T₂` (they are
  killed by `idealOf T₂`, by `vanishingIdeal_sup_pow_mul_le` and the ported theorem
  `forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top`). Then induction on `t`: a system
  killed by `(idealOf T)^(t+1)` has quotient by `idealOf T` killed by `idealOf T` (case `t = 1`) and `idealOf T`-part
  killed by `(idealOf T)^t` (same ported theorem), and `algebraised_of_quot_of_ker` concludes.

`solution`: `P` is noetherian; the ported theorem
`Scheme.IdealSheafData.exists_forall_ideal_pow_le_of_forall_le_radical` gives `e` with `(idealOf ⊤)^e = 0` on
affines, so every system is killed by `(idealOf ⊤)^e`, and `algebraised_of_killedBy ⊤ e` concludes.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.support_vanishingIdeal`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.radical_vanishingIdeal`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.isReduced_subscheme_vanishingIdeal`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.irreducibleSpace_subscheme_vanishingIdeal`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.isIntegral_subscheme_vanishingIdeal`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.compactSpace_of_isProper`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.isNoetherian_of_isProper`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.noetherianSpace_of_isProper`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.isProper_subschemeι`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.isProper_comp`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.isSeparated_of_isProper`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.idealAnnihilates_ker_subschemeι`
- private theorem `GEDriver.nonempty_orderedAffineCover_of_compactSpace_univ`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.exists_closeds_lt_sup_eq`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.vanishingIdeal_sup_pow_mul_le`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.vanishingIdeal_top_ideal_le_radical_bot`
- structure `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.AdicSys`
- def `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.AdicSys.Algebraised`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.algebraised_of_quot_of_ker`
- def `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.AdicSys.KilledBy`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.AdicSys.killedBy_one_iff`
- abbrev `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.idealOf`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.AdicSys.algebraised_of_forall_eq_zero`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.AdicSys.algebraised_of_killedBy_zero`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.AdicSys.algebraised_of_killedBy_coe_eq_empty`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.stepC`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.GEDriver.algebraised_of_killedBy`
- theorem `GEDriver.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_forall_exists_linearEquiv_tensorProduct_of_hom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ` (same contribution).
Other imports: `Mathlib`.
