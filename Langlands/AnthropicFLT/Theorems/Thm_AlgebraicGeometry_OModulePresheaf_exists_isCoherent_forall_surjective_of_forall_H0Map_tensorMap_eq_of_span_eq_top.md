# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.solution I ι hιq F hc hq φ hφs hφk d m σ hσ hgen`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top`:
let `A` be a commutative ring, `I` an ideal, `ι : P ⟶ ℙ^r_A` a closed immersion with `q = ι ≫ ProjSpace.π A r`
separated, `F : ℕ → OModulePresheaf q` coherent and quasi-coherent with maps `φ k : AffHom (F (k+1)) (F k)`
surjective on affine opens with kernel `I^(k+1) • ⊤`. Let `d, m ∈ ℕ` and `σ k l` (`l < m`) Čech `0`-cocycles of
`F k ⊗ O(d)` on `ProjSpace.stdCoverPullback ι`, compatible under `φ k ⊗ id` (`H0Map (σ (k+1) l) = σ k l`), whose
level-`0` components generate the sections over every chart of the cover. Then there are a coherent quasi-coherent
`E` and maps `θ k : AffHom E (F k)`, surjective on every affine open and compatible (`φ k ∘ θ (k+1) = θ k`).
(Concretely `E = O(-d)^m`; global generation of the twists gives a compatible system of surjections from a fixed
coherent sheaf.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top` (same contribution).
Other imports: `Mathlib`.
