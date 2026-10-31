/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.exists_iSup_preimage_eq_top_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {κ : Type u} (W : κ → X.Opens)
    (hcov : (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k) = ⊤) :
    ∃ (j : ι) (hij : i ≤ j), (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) = ⊤ := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit.solution ι _ _ _ G _ φ _ R _ g hR i X fX _ _ κ W hcov
