# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 21: `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry N.AlgebraicGeometry TopologicalSpace Opposite"` becomes `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 28: `p2m_export "AlgebraicGeometry" "…"` with 23 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 30: `p2m_open "AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry`.
  - FLT line 32: `p2m_open "AlgebraicGeometry.Scheme.Modules"` becomes `open AlgebraicGeometry.Scheme.Modules`.
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

`solution` states: for a module `𝓛` on `X_R` that is invertible in FLT's sense, there are `j ≥ i` and an
invertible module `𝓛_j` on `X_j` such that `cX^* 𝓛_j ≅ 𝓛` for every `cX : X_R ⟶ X_j` with the canonical
projections. This is FLT's descent of invertible sheaves to a finite stage of a direct limit; the proof module
`Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof` applies it, through the
theorem of `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`,
to the finitely generated subalgebras of a ring.

Proof as implemented.

1. `IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit` gives `j₀ ≥ i` and finitely many
   affine opens `W k` of `X_{j₀}` whose preimages under the canonical morphism `c₀ : X_R ⟶ X_{j₀}` cover
   `X_R` and carry frames `s k` of `𝓛`.
2. With `f₀ : X_{j₀} ⟶ Spec (G j₀)` the second projection, `X_R` is also the base change
   `X'_R = pullback f₀ (Spec.map (g j₀))`; the file builds the comparison isomorphism `e : X'_R ≅ X_R` from
   pullback lifts and replaces `𝓛` by `𝓛' = e^* 𝓛`, which is invertible and carries the transported frames
   `s' k` on the preimages of the `W k`.
3. `exists_unitCocycle_of_frames'` (namespace `FramesCocycle`): the transition functions of the frames form a
   unit cocycle `gc`. On `V a ⊓ V b` the coefficient `tr a b` is the unique function with
   `tr a b • s a = s b`; it exists and is unique because `s a` is a frame (`coeff_unique`, `coeff_eq`), and
   uniqueness gives `tr a a = 1` and the cocycle identity.
4. `UnitCocycle.exists_comap_eq_of_isDirectLimit`, applied at the base index `j₀` to `f₀`, to the
   quasi-compact (affine) opens `W k` and to `gc`, gives `j ≥ j₀` and a unit cocycle `c` on the preimages of
   the `W k` in `X'_j = pullback f₀ (Spec.map (φ j₀ j))`; these preimages cover `X'_j`, and the pullback of
   `c` to `X'_R` is `gc`.
5. `𝓛'_j = glueOfCocycle c` is invertible (`isInvertible_glueOfCocycle`). The helper
   `nonempty_pullback_glueOfCocycle_iso'` gives `cX'^* 𝓛'_j ≅ 𝓛'` for the canonical `cX' : X'_R ⟶ X'_j`:
   `exists_pullback_glueOfCocycle_iso` identifies the pullback with `glueOfCocycle (c.comap cX')`, whose
   frames have the same transition functions as the `s' k`, and the LB2 lemma
   `exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq` makes two modules with frames on a common cover and
   equal transition functions isomorphic (the transition condition is needed only for `a < b` in the linear
   order of `ULift (Fin n)`).
6. A second comparison isomorphism `ej : X'_j ≅ X_j` gives `𝓛_j = ej⁻¹^* 𝓛'_j`, invertible by
   `IsInvertible.pullback`. For `cX` with the canonical projections, `cX ≫ ej⁻¹ = e⁻¹ ≫ cX'`
   (`pullback.hom_ext`), and composing the pullback isomorphisms `pullbackComp`, `pullbackCongr` and
   `pullbackId` with `e⁻¹^*` of step 5 gives `cX^* 𝓛_j ≅ 𝓛`.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `coeff_unique`
- theorem `nonempty_pullback_glueOfCocycle_iso`
- theorem `nonempty_pullback_glueOfCocycle_iso'`
- abbrev `rL`
- theorem `rL_rL`
- theorem `rL_smul`
- def `tr`
- theorem `tr_spec`
- theorem `coeff_eq`
- theorem `tr_spec_le`
- theorem `tr_refl`
- theorem `tr_cocycle`
- theorem `exists_unitCocycle_of_frames'`
- theorem `isFrameOn_cast`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit`.
