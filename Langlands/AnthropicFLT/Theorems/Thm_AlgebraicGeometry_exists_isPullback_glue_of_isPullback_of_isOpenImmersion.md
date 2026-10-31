# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.solution` applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

States the gluing step: let `u₀ : U₀ ⟶ Spec R` and `v₀ : V₀ ⟶ Spec R` be quasi-compact, quasi-separated
and locally of finite presentation, glued along open immersions `a : W₀ ⟶ U₀`, `b : W₀ ⟶ V₀` over
`Spec R` with `a ≫ u₀` quasi-compact. Let `X` be covered by two opens `jU : U ⟶ X`, `jV : V ⟶ X` with
intersection `W`, and suppose `U` and `V` are the base changes of `U₀` and `V₀` along
`Spec A ⟶ Spec R` (pullback squares with `jU ≫ g`, `jV ≫ g`) compatibly with `W` and `W₀`. Then there
is a scheme `X₀` over `Spec R`, covered by open immersions of `U₀` and `V₀` meeting in `W₀`, whose
structure map `f₀` is quasi-compact, quasi-separated and locally of finite presentation, together with
`π : X ⟶ X₀` compatible with the charts, such that `X` is the base change of `X₀`
(`IsPullback π g f₀ (Spec.map (algebraMap R A))`). The proof term applies the companion solution
theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `AlgebraicGeometry.exists_isPullback_glue_of_isPullback_of_isOpenImmersion`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion`.
All modules also import `Mathlib`.
