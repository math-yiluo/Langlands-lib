# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.solution I q p K' F' φ' G' hG'c hG'q ψ' hψ's hψ'k hψ'c F φ hφs hφk v hvc`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`:
let `A` be a noetherian commutative ring with an ideal `I`, `q : P ⟶ Spec A` and `p : V' ⟶ P` proper, `K'` an
ordered affine cover of `V'`. Let `G'` be a coherent quasi-coherent FLT presheaf over `p ≫ q` with surjections
`ψ' k : G' → F' k` on affines of kernel `I^(k+1) • ⊤`, compatible with transition maps `φ'` of the `F' k`. Let
`F k` be an adic system on `P` (transition maps `φ k` surjective on affines with kernel `I^(k+1) • ⊤`) and
`v k : F k → cechPushforward p q K' (F' k)` compatible maps. Then the Čech pushforward `GP` of `G'` is coherent
and quasi-coherent, and there are a coherent quasi-coherent adic system `Ps` on `P` (transition maps `π`) and
maps `ψP k : GP → Ps k` (surjective on affines, kernel `I^(k+1) • ⊤`, compatible with `π`),
`ν k : Ps k → cechPushforward (F' k)` (compatible with `π` and `φ'`, with `ν k ∘ ψP k` the Čech pushforward of
`ψ' k`, and with kernel of `ν (k+c)` in `I^(k+1) • ⊤` for some `c` depending on the affine open and `k`), and
`u k : F k → Ps k` (compatible with `φ` and `π`, with `ν k ∘ u k = v k`). (In effect `Ps k = GP / I^(k+1) GP`,
and `u` factors `v` through it.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper` (same contribution).
Other imports: `Mathlib`.
