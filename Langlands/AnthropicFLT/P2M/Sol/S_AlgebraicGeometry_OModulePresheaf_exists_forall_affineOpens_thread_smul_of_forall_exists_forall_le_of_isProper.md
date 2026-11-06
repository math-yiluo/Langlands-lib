# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- `p2m_open` also opens namespaces of this module before they exist (later commands create them): `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry`. Lean's `open` rejects a namespace that does not exist yet, so each of them is registered by an empty block `namespace N end N` right after the options; the `open` then has the FLT effect.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper`.

Proof. Section `BasicCover` (namespace `AlgebraicGeometry.OModulePresheaf` inside the solution namespace), for
an FLT presheaf `F` that is "quasi-coherent on basic opens" of an affine `W` (the two localisation properties
for every `g : Γ(P, W)`) and a finite family `f` generating the unit ideal: a section vanishing on every `D(f l)`
is `0` (`eq_zero_of_forall_res_basicOpen_eq_zero`), and sections on the `D(f l)` that agree on the overlaps
glue (`exists_forall_res_basicOpen_eq`; with `exists_sum_mul_pow_eq_one`, `pow_smul_eq_zero_of_le`,
`res_inf_eq_left`, `res_inf_eq_right`). Namespace `C3Glue`: restriction lemmas, `mem_pow_ideal_of_le` (powers
of the vanishing ideal restrict to powers), `span_range_comp_eq_top`, and `chart_basicOpen_eq` (the chart over
`D(f)` is the basic open of the image of `f` in the chart over `W`).

`solution`: `P` is quasi-compact, so finitely many affine opens `t` cover it; with `Nf W₀` the exponents from
`hloc`, take `N := 2 · max_{W₀ ∈ t} Nf W₀`. For an affine `W`, choose `f : ι → Γ(P, W)` generating the unit ideal
with each `D(f l)` inside some `W₀ ∈ t`. Existence: the set of `a` for which a thread `m` with
`v n (m n) = a • ℓ n` exists is an ideal (`Sgood`); for `x, y` in the `(max Nf)`-th power of the vanishing ideal,
`hloc` on the `D(f l)` gives threads `ml l` for `y`; multiplied by `x` they agree on the overlaps
`D(f l f l')` (by the injectivity part of `hloc` there), glue to threads `m` over `W` by quasi-coherence of the
`F n` (`hFq`), and `v n (m n) = (x y) • ℓ n` is checked chartwise on the basic opens of the charts, which are
quasi-coherent by the ported `forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct`.
So the product ideal, which contains the `N`-th power, lies in `Sgood`. Injectivity: restrict to the `D(f l)`
and apply the injectivity part of `hloc` there, then `eq_zero_of_forall_res_basicOpen_eq_zero`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.toD`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.isUnit_toD`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.presheaf_map_map`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.exists_sum_mul_pow_eq_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.pow_smul_eq_zero_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.res_inf_eq_left`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.res_inf_eq_right`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.exists_forall_res_basicOpen_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.C3Glue.res_eq_zero_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.C3Glue.map_map_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.C3Glue.mem_pow_ideal_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.OModulePresheaf.C3Glue.span_range_comp_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.AlgebraicGeometry.OModulePresheaf.C3Glue.chart_basicOpen_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.AlgebraicGeometry.AlgebraicGeometry.OModulePresheaf.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct` (same contribution).
Other imports: `Mathlib`.
