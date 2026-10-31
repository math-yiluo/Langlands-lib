# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit`

## Source

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands.
  - FLT line 28: `p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.solution` becomes `exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.solution ι _ _ _ G _ φ _ R _ g hR i X fX _ _ 𝓛 h𝓛`. `p2m_exact_reverting` reverts the whole local context and elaborates the term against the reverted goal; `exact` applies the same term to the same hypotheses in the same order (`_` for anonymous hypotheses such as instances).
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit`

## Statement

Common setting: `ι` is a nonempty directed preorder, `G : ι → Type u` a directed system of commutative rings with transition maps `φ i j hij`, and `R` a commutative ring with maps `g i : G i →+* R` such that `R` is the direct limit (`hR : IsDirectLimit …`, from `Def_Mathlib_Algebra_IsDirectLimit`). Fix an index `i` and a quasi-compact, quasi-separated morphism `fX : X ⟶ Spec (G i)`. Write `X_R` for `pullback fX (Spec.map (g i))` (the base change of `X` to `Spec R`), `X_j` for `pullback fX (Spec.map (φ i j hij))` when `i ≤ j`, and `p_R`, `p_j` for their first projections to `X`. A comparison map is any `c : X_R ⟶ X_j` with `c ≫ p_j = p_R` and `c ≫ pullback.snd = pullback.snd ≫ Spec.map (g j)`; the statements quantify over all such maps.

If `𝓛` is an `IsInvertible` (from `Def_AlgebraicGeometry_RelativePicardFunctor`) module on `X_R`, then there are `j ≥ i`, `n : ℕ` and affine opens `W : ULift (Fin n) → X_j.Opens` such that, for every comparison map `c`, the opens `c ⁻¹ᵁ W k` cover `X_R` and `𝓛` has a frame `s k` on each `c ⁻¹ᵁ W k` (`IsFrameOn s V`, from `Def_AlgebraicGeometry_ModulesSectionsTensor`: for every open `W ≤ U` with `W ≤ V`, `g ↦ g • s|W` is a bijection `Γ(X, W) → Γ(M, W)`).

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit`.
