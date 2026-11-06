# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- `p2m_open` also opens namespaces of this module before they exist (later commands create them): `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry`. Lean's `open` rejects a namespace that does not exist yet, so each of them is registered by an empty block `namespace N end N` right after the options; the `open` then has the FLT effect.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward`.

Proof. Namespace `AlgebraicGeometry.OModulePresheaf.C3Asm` (inside the solution namespace). Section `Threads`:
`IsThread F φ U s` says that `s n ∈ F n (U)` is compatible under the `φ n`; when the `φ n` are surjective on
affines every element at level `k` lies in some thread (`exists_isThread`, built recursively by `seq0` and
`seqMod`), and two threads with the same level-`k` value differ by elements of `I^(k+1) • ⊤`
(`IsThread.sub_mem`). Section `Levels`: `J • ⊤` is preserved by linear maps (`smul_top_mem_map`), is `0` in
the target of a surjection with kernel `J • ⊤` (`eq_zero_of_mem_smul_top`), and descends along a thread
(`thread_mem_down`).

`solution`, with `N` from `hunif`. Existence: for `y ∈ Ps k (W)` take a thread `yy` through `y` in `Ps`;
`ν` maps it to a compatible family `ℓ` of Čech sections, and `hunif` gives a thread `m` in `F` with
`v n (m n) = a • ℓ n`. The differences `δ n = u n (m n) - a • yy n` form a thread killed by `ν`, so by `hνi`
`δ (k+c) ∈ I^(k+1) • ⊤`, hence `δ k ∈ I^(k+1) • ⊤` (`thread_mem_down`), which is `0` in `Ps k`
(`eq_zero_of_mem_smul_top` with `ψP k`); thus `u k (m k) = a • y`. Kernel bound: the ported theorem
`exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top` gives an approximate kernel
system `Ks` of `u` with constant `c` on `W`; for `x` in the kernel of `u (k+c)`, write
`x = j (k+c) y + x₁` with `x₁ ∈ I^(k+1) • ⊤`, extend `y` to a thread in `Ks`, whose image under `j` is a thread
in `F` killed by `v`; the second half of `hunif` shows that `a` kills it, the kernel bound for `j` and
`thread_mem_down` give `a • y = 0`, and `a • x = a • x₁ ∈ I^(k+1) • ⊤`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.IsThread`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.seq0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.seqMod`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.seqMod_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.seqMod_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.seqMod_at`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.exists_isThread`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.IsThread.sub_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.smul_top_mem_map`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.eq_zero_of_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.OModulePresheaf.C3Asm.thread_mem_down`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
