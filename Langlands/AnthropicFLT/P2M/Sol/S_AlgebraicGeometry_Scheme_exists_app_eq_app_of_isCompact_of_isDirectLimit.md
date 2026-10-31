# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit`.
  - FLT line 23: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.appInf" "AlgebraicGeometry.Scheme.Hom.appInf"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
  - FLT line 24: `p2m_open "AlgebraicGeometry.Scheme.Modules"` becomes `open AlgebraicGeometry.Scheme.Modules`.
  - FLT line 29: `p2m_alias "N.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf" "AlgebraicGeometry.Scheme.Hom.preimage_mono_inf"` is deleted. It made `N.…` an alias of the private declaration declared just above. Nothing in the file refers to the alias name, and the file compiles without it.
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

`solution` states: let `W` be a quasi-compact open of `X`, let `j ≥ i`, and let `t, t'` be sections of the
structure sheaf of `X_j` over `p_j⁻¹ W` whose pullbacks `c^* t` and `c^* t'` agree for every
`c : X_R ⟶ X_j` with the canonical projections. Then there is `j' ≥ j` such that `c^* t = c^* t'` for every
`c : X_{j'} ⟶ X_j` with the canonical projections (`c ≫ p_j = p_{j'}`, and the second projections are related
by `Spec.map (φ j j')`). In words: two sections over a quasi-compact open that agree in the limit already
agree at a finite stage.

Proof as implemented. As in the companion files, the index set is restricted to `{j // i ≤ j}` and all
rings become `G i`-algebras. The helper `nat_gamma` shows that, under the isomorphisms
`Γ(X_H, p_H⁻¹ V) ≃ Γ(X, V) ⊗[G i] H` of the LB2 lemma
`exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen` (for affine `V` and `G i`-algebras
`H`), pullback along a morphism `X_{H'} ⟶ X_H` with the canonical projections corresponds to `ψ ⊗ id` for
the algebra map `ψ : H → H'`; it is checked on pure tensors `a ⊗ h = (a ⊗ 1)(1 ⊗ h)`. Write `W` as a finite
union of affine opens `V ∈ S`. The hypothesis, applied to the canonical morphism `c₀ : X_R ⟶ X_j`, shows that
the restrictions of `t` and `t'` to `p_j⁻¹ V` have equal images in `R ⊗ Γ(X, V)`, the direct limit of the
`G m ⊗ Γ(X, V)` (LB2 lemma `Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit`). Hence their images
agree at some stage `m(V) ≥ j`. Let `j'` be a common upper bound of these finitely many stages. For `c` as
in the conclusion, `nat_gamma` shows that `c^* t` and `c^* t'` agree on each `p_{j'}⁻¹ V`; these opens cover
`p_{j'}⁻¹ W = c⁻¹(p_j⁻¹ W)`, so the two sections agree by the sheaf property. The further helpers
`res_injective_of_eq`, `appLE_app_of_comp_eq` and `appLE_appLE_of_comp_eq` are restriction and composition
identities for sections; the block `LimitIsoFil` also contains the helpers described in
`S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit`.

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

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen`, `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit`.
