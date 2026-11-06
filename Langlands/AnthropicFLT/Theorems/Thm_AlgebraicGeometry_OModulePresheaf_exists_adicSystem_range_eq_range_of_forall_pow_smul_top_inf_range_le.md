# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.solution I F φ hφs hφk L hLc hLq ι hιi lam hls hlc hAR`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le`:
let `A` be a commutative ring with an ideal `I`, `q : P ⟶ Spec A`, and `F n` an adic system of FLT presheaves
over `q` (transition maps `φ n` surjective on affine opens with kernel `I^(n+1) • ⊤`). Let `L n` be coherent
quasi-coherent presheaves with injective maps `ι n : AffHom (L n) (F n)` on affines and surjective
transition maps `lam n` compatible with `φ` (`ι n ∘ lam n = φ n ∘ ι (n+1)`). Assume an Artin–Rees condition
`hAR`: on each affine `U` there is `c` with `I^n • ⊤ ⊓ range (ι n) ≤ I^k • range (ι n)` whenever `k + c ≤ n`.
Then there is a coherent quasi-coherent adic system `Ks k` (transition maps `κ k` surjective on affines with
kernel `I^(k+1) • ⊤`) with maps `j k : AffHom (Ks k) (F k)` compatible with `κ` and `φ`, with the same range
as `ι k` on affines, and with `ker (j n) ≤ I^(k+1) • ⊤` on each affine `U` once `k + c ≤ n` (for some `c`
depending on `U`).

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le` (same contribution).
Other imports: `Mathlib`.
