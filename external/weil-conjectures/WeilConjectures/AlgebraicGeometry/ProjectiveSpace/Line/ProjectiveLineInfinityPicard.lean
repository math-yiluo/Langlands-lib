/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.P1DiagonalLocalIdeal
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSectionChart
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-! # The divisor line of the infinity section

## References

* Stacks Project, Tag 01X0
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProjectiveLine
open ProjectiveSpace Scheme.Modules

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace

private lemma infinity_sections (S : Scheme.{u}) :
    infinity S = homOfSections (𝟙 S) (pairSections 1 0)
      (span_range_one_pairSections 0) := by
  exact homOfVector_comp_infinityChart (𝟙 S) 0

private lemma infinity_ratio {S X : Scheme.{u}} (g : X ⟶ S)
    (h : ⊤ ≤ (g ≫ infinity S) ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩)
    (k : ULift.{u} (Fin 2)) :
    (g ≫ infinity S).appLE _ ⊤ h (coordRatio (ULift.{u} (Fin 2)) S ⟨0⟩ k) =
      pairSections (1 : Γ(X, ⊤)) 0 k := by
  have he := congrArg (fun f ↦ g ≫ f) (infinity_sections S)
  simp only [comp_homOfSections, Category.comp_id] at he
  rw [ProjectiveSpace.appLE_eq_of_eq he _ _ h]
  have hr := homOfSections_appLE_coordRatio g
    (fun i ↦ g.appTop.hom (pairSections (1 : Γ(S, ⊤)) 0 i))
    (span_range_appTop_eq_top g (span_range_one_pairSections 0))
    (i := ⟨0⟩) (by simp) k (he ▸ h)
  refine hr.trans ?_
  rcases k with ⟨k⟩
  fin_cases k <;> simp [pairSections]

private lemma infinity_chart {S X : Scheme.{u}} (g : X ⟶ S) :
    ⊤ ≤ (g ≫ infinity S) ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩ := by
  rw [infinity_sections, comp_homOfSections, homOfSections_preimage_standardOpen]
  simp

private lemma infinity_ideal (S : Scheme.{u}) [IsNoetherian S] (i : ULift.{u} (Fin 2))
    (U : (ProjectiveLine S).affineOpens)
    (hi : U.1 ≤ standardOpen (ULift.{u} (Fin 2)) S i) :
    (infinity S).ker.ideal U = Ideal.span
      {(ProjectiveLine S).presheaf.map (homOfLE hi).op (coordRatio _ S i ⟨1⟩)} := by
  apply ProjectiveSpace.kernel_ideal_eq_span_of_test
  intro X g hg
  have hgi : ⊤ ≤ g ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) S i :=
    hg.trans (g.preimage_mono hi)
  have hmap : g.appLE U.1 ⊤ hg
      ((ProjectiveLine S).presheaf.map (homOfLE hi).op (coordRatio _ S i ⟨1⟩)) =
      g.appLE _ ⊤ hgi (coordRatio _ S i ⟨1⟩) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rw [hmap]
  constructor
  · intro hz
    refine ⟨g ≫ ProjectiveLine S ↘ S, ?_⟩
    symm
    have hj := infinity_chart (S := S) (X := X) (g ≫ ProjectiveLine S ↘ S)
    apply ProjectiveSpace.chart_eq_of_det_zero (S := S) (X := X) g
      ((g ≫ ProjectiveLine S ↘ S) ≫ infinity S) i ⟨0⟩ hgi hj
    · simp only [Category.assoc, infinity_over, Category.comp_id]
    · simp only [infinity_ratio, pairSections_one, pairSections_zero, mul_zero,
        mul_one, hz, sub_self]
  · rintro ⟨h, rfl⟩
    rw [ProjectiveSpace.pull_ratio_mul (h ≫ infinity S) i ⟨0⟩ ⟨1⟩ hgi
      (infinity_chart h), infinity_ratio, pairSections_one, zero_mul]

/-- The line bundle of the infinity divisor is O(1), over a Noetherian base. -/
theorem infinity_picard (S : Scheme.{u}) [IsNoetherian S]
    (hI : (infinity S).ker.IsInvertible) :
    letI := hI.isInvertible_dual_toModules
    Scheme.Pic.ofIsInvertible (Scheme.Modules.dual (infinity S).ker.toModules) =
      Scheme.Pic.ofIsInvertible (twist (ULift.{u} (Fin 2)) S 1) := by
  let := hI.isInvertible_dual_toModules
  let φ := coordinateSection (ULift.{u} (Fin 2)) S ⟨1⟩
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ (ProjectiveLine S).Modules) :=
    IsInvertible.sheafOfModules_isInvertible _
  have : SheafOfModules.IsInvertible.{u, u, u}
      (twist (ULift.{u} (Fin 2)) S 1) :=
    IsInvertible.sheafOfModules_isInvertible _
  have hz : (infinity S).ker = φ.zeroLocus := by
    let C := {U : (ProjectiveLine S).affineOpens //
      ∃ i : ULift.{u} (Fin 2), U.1 ≤ standardOpen (ULift.{u} (Fin 2)) S i}
    have hcov : ⨆ c : C, c.val.1 = ⊤ := by
      apply eq_top_iff.mpr
      intro x _
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_standardOpen (ULift.{u} (Fin 2)) S).ge (show x ∈ ⊤ from trivial))
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
        (ProjectiveLine S).isBasis_affineOpens.exists_subset_of_mem_open hi
          (standardOpen (ULift.{u} (Fin 2)) S i).2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVW⟩, hxV⟩
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun c : C ↦ c.val) hcov
    intro c
    obtain ⟨i, hi⟩ := c.property
    have he := Hom.app_presheaf_map φ (homOfLE hi) (1 : Γ(ProjectiveLine S, _))
    change φ.app c.val.1
        ((ProjectiveLine S).presheaf.map (homOfLE hi).op 1) =
      (twist (ULift.{u} (Fin 2)) S 1).presheaf.map (homOfLE hi).op
        (φ.app (standardOpen (ULift.{u} (Fin 2)) S i)
          (1 : Γ(ProjectiveLine S, standardOpen (ULift.{u} (Fin 2)) S i))) at he
    rw [map_one] at he
    dsimp only [φ] at he
    rw [coordinateSection_app_standardOpen] at he
    rw [Scheme.Modules.map_smul] at he
    rw [infinity_ideal S i c.val hi]
    exact (φ.ideal_zeroLocus c.val (isFreeGenerator_one c.val.1)
      ((isFreeGenerator_twistGenerator (ULift.{u} (Fin 2)) S 1 i).map hi) he).symm
  have hφ : φ.zeroLocus.IsInvertible := hz ▸ hI
  obtain ⟨e⟩ := φ.nonempty_iso_dual_toModules_tensorObj hφ
  rw [← hz] at e
  exact Scheme.Pic.ofIsInvertible_eq_of_iso (e ≪≫ ρ_ _).symm

end AlgebraicGeometry.ProjectiveLine
