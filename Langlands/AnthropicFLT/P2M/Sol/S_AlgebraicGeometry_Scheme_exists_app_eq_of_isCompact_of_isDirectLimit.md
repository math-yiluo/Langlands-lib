# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit`.
  - FLT line 24: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.appInf" "AlgebraicGeometry.Scheme.Hom.appInf"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
  - FLT line 25: `p2m_open "AlgebraicGeometry.Scheme.Modules"` becomes `open AlgebraicGeometry.Scheme.Modules`.
  - FLT line 30: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf" "AlgebraicGeometry.Scheme.Hom.preimage_mono_inf"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
- No other change: the declarations, statements and proofs are the FLT text.

## Mathematical content

Setting shared by the FLT direct-limit lemmas. `ι` is a nonempty directed preorder, `(G j, φ j k)` is a
directed system of commutative rings in `Type u`, and the ring maps `g j : G j →+* R` satisfy FLT's
`IsDirectLimit` (ported module `Definitions.Def_Mathlib_Algebra_IsDirectLimit`): every element of `R` is
some `g j x`, two elements of stages with the same image in `R` become equal at a common later stage, and
`g k ∘ φ j k = g j`. For `i : ι`, `fX : X ⟶ Spec (G i)` is quasi-compact and quasi-separated
(`Spec (G i)` abbreviates `Spec (CommRingCat.of (G i))`). For `j ≥ i` write `X_j` for Mathlib's chosen
pullback `pullback fX (Spec.map (φ i j))` and `X_R` for `pullback fX (Spec.map (g i))`, with first
projections `p_j : X_j ⟶ X` and `p_R : X_R ⟶ X`. A morphism `c : X_R ⟶ X_j` *with the canonical
projections* is one with `c ≫ p_j = p_R` and `c ≫ (second projection of X_j) = (second projection of X_R) ≫
Spec.map (g j)`. By the universal property of the pullback there is exactly one such `c`; the statements
nevertheless quantify over all of them.

`solution` states: for a quasi-compact open `W` of `X` and a section `s` of the structure sheaf of `X_R`
over `p_R⁻¹ W`, there are `j ≥ i` and a section `t` of the structure sheaf of `X_j` over `p_j⁻¹ W` such
that, for every `c : X_R ⟶ X_j` with the canonical projections, `c^* t`, transported along the equality
`p_R⁻¹ W = c⁻¹(p_j⁻¹ W)`, equals `s`. In words: sections over a quasi-compact open of the limit descend to a
finite stage.

Proof as implemented. The reductions and the helpers (`nat_gamma` and the restriction identities) are those
of `S_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit`. Write `W` as a finite union
of affine opens `V ∈ S`. On each `V`, the restriction of `s` corresponds to an element of
`R ⊗[G i] Γ(X, V)`, the direct limit of the `G j ⊗ Γ(X, V)`, so it comes from some stage. Push the finitely
many lifts to a common stage `j₀` and transport them back to sections `t_V` over `p_{j₀}⁻¹ V`; they pull back
to the restrictions of `s` along the canonical morphism `c₀ : X_R ⟶ X_{j₀}` (any morphism with the canonical
projections equals `c₀`). Because `X` is quasi-separated, each `V ⊓ V'` is quasi-compact; the restrictions of
`t_V` and `t_{V'}` to `p_{j₀}⁻¹(V ⊓ V')` have the same pullback to `X_R` (both are restrictions of `s`), so by
`AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit` they agree after pullback to some
stage `j(V, V')`. Let `js` be an upper bound of `j₀` and all `j(V, V')`. Pulled back to `X_{js}`, the `t_V`
form a compatible family for the cover of `p_{js}⁻¹ W` by the opens `p_{js}⁻¹ V` and glue (sheaf property) to
`t`. For `c : X_R ⟶ X_{js}` with the canonical projections, `c` followed by the transition morphism
`X_{js} ⟶ X_{j₀}` is `c₀`, so `c^* t` and `s` agree on each `p_R⁻¹ V` and hence on `p_R⁻¹ W`.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- private def `_root_.AlgebraicGeometry.Scheme.Hom.appInf`
- private theorem `_root_.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf`
- lemma `appInf_res`
- lemma `res_res`
- lemma `cocycle_res`
- lemma `map_swap`
- lemma `map_one_tmul`
- lemma `exists_ge₂`
- lemma `nonempty_iso_pullback_of_fac`
- lemma `res_injective_of_eq`
- lemma `appLE_app_of_comp_eq`
- lemma `appLE_appLE_of_comp_eq`
- lemma `nat_gamma`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen`, `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit`.
