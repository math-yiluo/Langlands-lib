# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit`.
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

`solution` states: if `W : κ → X.Opens` is a family of opens of `X` whose preimages `p_R⁻¹(W k)` cover
`X_R`, then for some `j ≥ i` the preimages `p_j⁻¹(W k)` cover `X_j`.

Proof as implemented. The index set is restricted to `J = {j // i ≤ j}`, every `G j` becomes a
`G i`-algebra through `φ i j`, and `R` is again the direct limit of the restricted system. Since `X` is
quasi-compact, it is a finite union of affine opens `Y ∈ S`. Fix such a `Y` and let `H` be the set of
`h ∈ Γ(X, Y)` whose basic open `D(h)` lies in some `W k`. The LB2 lemma
`exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen` gives algebra isomorphisms
`Γ(X_R, p_R⁻¹ Y) ≃ R ⊗[G i] Γ(X, Y)` sending `p_R^* h` to `1 ⊗ h`, and likewise for every `X_j`. The basic
opens `D(h) ⊆ W k` with `h ∈ H` cover `Y ∩ ⋃ W k`, so their preimages, the basic opens of the elements
`p_R^* h`, cover the affine open `p_R⁻¹ Y`; hence these elements generate the unit ideal, and
`1 = Σ_m c_m · p_R^* h_m` for finitely many `h_m ∈ H`. By the LB2 lemma
`Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit`, `R ⊗ Γ(X, Y)` is the direct limit of the
`G j ⊗ Γ(X, Y)`. The finitely many coefficients come from a common stage `j₀` (helper `exists_ge₂`: finitely
many indices of a directed set have a common upper bound), and the identity `Σ z_m (1 ⊗ h_m) = 1`, which
holds in the limit, already holds at some stage `j₁ ≥ j₀`. For every `j ≥ j₁` its image under the
transition maps shows that the elements `p_j^* h_m` generate the unit ideal of `Γ(X_j, p_j⁻¹ Y)`, so
`p_j⁻¹ Y` is covered by the basic opens `D(p_j^* h_m) = p_j⁻¹ D(h_m) ⊆ p_j⁻¹(W k)`. A common upper bound of
the finitely many indices `j₁(Y)` is the required `j`.

The block `LimitIsoFil` collects helper lemmas that FLT repeats in several of these files: restriction
identities for sections (`appInf`, `preimage_mono_inf`, `appInf_res`, `res_res`, `cocycle_res`), identities
for tensor products of algebra maps (`map_swap`, `map_one_tmul`), `exists_ge₂`, and
`nonempty_iso_pullback_of_fac` (if the pullbacks of two modules along `π` are isomorphic, so are their
pullbacks along any `p = h ≫ π`).

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
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen`, `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit`.
