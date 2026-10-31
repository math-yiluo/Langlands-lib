# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit`

## Source

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands.
  - FLT line 31: `p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit.solution` becomes `exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit.solution ι _ _ _ G _ φ _ R _ g hR i X fX _ _ W hW j hij t t' h`. `p2m_exact_reverting` reverts the whole local context and elaborates the term against the reverted goal; `exact` applies the same term to the same hypotheses in the same order (`_` for anonymous hypotheses such as instances).
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit`

## Statement

Common setting: `ι` is a nonempty directed preorder, `G : ι → Type u` a directed system of commutative rings with transition maps `φ i j hij`, and `R` a commutative ring with maps `g i : G i →+* R` such that `R` is the direct limit (`hR : IsDirectLimit …`, from `Def_Mathlib_Algebra_IsDirectLimit`). Fix an index `i` and a quasi-compact, quasi-separated morphism `fX : X ⟶ Spec (G i)`. Write `X_R` for `pullback fX (Spec.map (g i))` (the base change of `X` to `Spec R`), `X_j` for `pullback fX (Spec.map (φ i j hij))` when `i ≤ j`, and `p_R`, `p_j` for their first projections to `X`. A comparison map is any `c : X_R ⟶ X_j` with `c ≫ p_j = p_R` and `c ≫ pullback.snd = pullback.snd ≫ Spec.map (g j)`; the statements quantify over all such maps.

Let `W` be a quasi-compact open of `X`, `j ≥ i`, and `t`, `t'` sections of the structure sheaf of `X_j` over `p_j ⁻¹ᵁ W` whose pullbacks along every comparison map `X_R ⟶ X_j` agree. Then there is `j' ≥ j` such that the pullbacks of `t` and `t'` along every map `c : X_j' ⟶ X_j` with `c ≫ p_j = p_j'` and `c ≫ pullback.snd = pullback.snd ≫ Spec.map (φ j j' _)` agree.

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit`.
