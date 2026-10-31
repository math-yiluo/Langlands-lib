# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 11: `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry N.AlgebraicGeometry TopologicalSpace Opposite"` becomes `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The one reference that relied on it is written with a longer name instead (last bullet below).
  - FLT line 368: `p2m_reactivate "N.DirLimSpread"` becomes `open scoped N.DirLimSpread`. `p2m_reactivate` first removes the namespace from the active scopes and then activates it again; `open scoped` only activates it. With this file the difference does not matter.
  - FLT line 370: `p2m_export "AlgebraicGeometry" "…"` with 20 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 370: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 9 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names.
  - FLT line 370: `p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf IsFrameOn IsInvertible IsInvertible.exists_isFrameOn"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (hom_ext pullback presheaf IsFrameOn IsInvertible IsInvertible.exists_isFrameOn)`.
  - FLT line 371: `p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in` becomes `open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Modules in`; both only activate the scoped declarations of the namespace for the next command.
- In the proof of `solution` (FLT line 441), `Scheme.Modules.exists_isFrameOn_congr` is written `AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_congr`. The lemma is declared in this file, so its full name is `N.AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_congr`. FLT found it through the open namespace `N.AlgebraicGeometry`, which is omitted above. The longer name resolves to the same lemma from inside `N`.
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

`solution` states: for a module `𝓛` on `X_R` that is invertible in FLT's sense, there are `j ≥ i`, `n : ℕ`
and affine opens `W k` of `X_j` (`k : ULift (Fin n)`) such that, for every `c : X_R ⟶ X_j` with the canonical
projections, the preimages `c⁻¹(W k)` cover `X_R` and each `c⁻¹(W k)` carries a frame of `𝓛` (a section
`s k` with `IsFrameOn (s k) (c⁻¹(W k))`).

Proof as implemented. The namespace `DirLimSpread` presents `X_R` as a cofiltered limit of the `X_j`: the
rings `G j` with the maps `g j` form a colimit cocone (`isColimitRingCocone`, built from `IsDirectLimit`
through filtered colimits of types), `Spec` turns it into a limit cone (`isLimitSpecCone`, since `Spec`
preserves limits as a right adjoint), and the diagram `D` of the pullbacks `X_j` over `{j // i ≤ j}ᵒᵖ` with
the cone `c` of canonical morphisms is a limit (`isLimitCone`, by Mathlib's
`isLimitOfIsPullbackOfIsConnected`, because each `X_j` is the pullback of `Spec (G j)` along `fX`). Its
transition maps are affine morphisms, and every `X_j` is quasi-compact and quasi-separated (scoped
instances). `isDirectLimit'` restricts the direct limit to the indices above `i`. The file also proves
`exists_open_core` (a quasi-compact open of `X_R` is the preimage of a quasi-compact open of some `X_j`,
from Mathlib's `exists_preimage_eq`); the main proof does not use it.

Main argument: by `IsInvertible.exists_isFrameOn` every point of `X_R` has an open neighbourhood with a frame,
and since affine opens form a basis and frames restrict to frames, the affine opens of `X_R` that carry a
frame cover `X_R`. Mathlib's `Scheme.exists_isOpenCover_and_isAffine`, applied to the limit cone, gives a
stage `j`, a finite subset `S` of these affine opens and affine opens `V A` (`A ∈ S`) covering `X_j` with
`A = c_j⁻¹(V A)`. Enumerating `S` by `ULift (Fin |S|)` gives `n` and `W`. A morphism `c : X_R ⟶ X_j` with
the canonical projections equals the limit projection `c_j` (`pullback.hom_ext`), so `c⁻¹(W k)` is the
corresponding `A`. These opens cover `X_R` because the `V A` cover `X_j`, and each carries a frame by the
choice of `S` (`exists_isFrameOn_congr` transports a frame along an equality of opens).

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `φ_self`
- theorem `φ_comp`
- def `ringDiag`
- def `ringCocone`
- def `specDiag`
- theorem `specDiag_obj`
- theorem `specDiag_map`
- def `isColimitRingCocone`
- def `specCone`
- theorem `specCone_pt`
- theorem `specCone_π`
- def `isLimitSpecCone`
- abbrev `sφ`
- abbrev `sg`
- theorem `sφ_irrel`
- theorem `sg_comp`
- theorem `sφ_comp`
- theorem `sφ_self`
- def `D`
- def `t`
- theorem `D_obj`
- theorem `D_map_fst`
- theorem `D_map_snd`
- theorem `t_app`
- theorem `isPullback_D_map`
- def `α`
- def `c`
- theorem `c_pt`
- theorem `c_π_fst`
- theorem `c_π_snd`
- theorem `isPullback_c_π`
- def `isLimitCone`
- def `proj`
- def `fstL`
- def `sndL`
- theorem `proj_def`
- theorem `fstL_def`
- theorem `sndL_def`
- theorem `t_appL`
- theorem `hom_extL`
- theorem `conditionL`
- def `liftL`
- theorem `liftL_fstL`
- theorem `liftL_sndL`
- theorem `D_map_eq`
- theorem `D_map_fstL`
- theorem `D_map_sndL`
- theorem `D_map_map`
- theorem `proj_map`
- theorem `proj_fstL`
- theorem `proj_sndL`
- def `homOp`
- theorem `exists_open_core`
- abbrev `J`
- abbrev `φ'`
- abbrev `g'`
- abbrev `bot`
- theorem `bot_le`
- theorem `isDirectLimit'`
- theorem `AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_congr`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn`.
