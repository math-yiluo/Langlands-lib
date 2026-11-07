import Langlands.AlgebraicGeometry.IntegralSchemePushoutGlobal

/-! # Descending the properties of compatible affine pushout models -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout.CompatibleAffinePushoutAtlas

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    (D : CompatibleAffinePushoutAtlas i j)

/-- Properties local on the target descend from the left model maps. -/
lemma left_property (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ t, P (D.inl t)) : P D.left := by
  apply IsZariskiLocalAtTarget.of_openCover D.openCover
  intro t
  change P (pullback.snd D.left (D.chart t))
  rw [← P.cancel_left_of_respectsIso (D.isPullback_left t).isoPullback.hom,
    (D.isPullback_left t).isoPullback_hom_snd]
  exact hP t

/-- Properties local on the target descend from the right model maps. -/
lemma right_property (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ t, P (D.inr t)) : P D.right := by
  apply IsZariskiLocalAtTarget.of_openCover D.openCover
  intro t
  change P (pullback.snd D.right (D.chart t))
  rw [← P.cancel_left_of_respectsIso (D.isPullback_right t).isoPullback.hom,
    (D.isPullback_right t).isoPullback_hom_snd]
  exact hP t

/-- Integral left model maps give an integral global cocone leg. -/
lemma left_isIntegral (hP : ∀ t, IsIntegralHom (D.inl t)) : IsIntegralHom D.left :=
  D.left_property @IsIntegralHom hP

/-- Closed right model maps give a closed global cocone leg. -/
lemma right_isClosedImmersion (hP : ∀ t, IsClosedImmersion (D.inr t)) :
    IsClosedImmersion D.right :=
  D.right_property @IsClosedImmersion hP

/-- The left opens of the atlas form an open cover. -/
def leftOpenCover : X.OpenCover where
  I₀ := D.Index
  X t := (D.leftOpen t).toScheme
  f t := (D.leftOpen t).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨t, ht⟩ := D.covers_left x
    exact ⟨t, ⟨x, ht⟩, rfl⟩

/-- Cartesian affine model squares give the global pullback square. -/
lemma isPullback_global
    (hP : ∀ t, IsPullback (CompatibleOpen.leftMap i (D.leftOpen t))
      (CompatibleOpen.rightMap i j (D.leftOpen t) (D.rightOpen t) (D.compatible t))
      (D.inl t) (D.inr t)) : IsPullback i j D.left D.right := by
  apply Scheme.isPullback_of_openCover i j D.left D.right D.leftOpenCover
  intro t
  have ht := (hP t).paste_vert (D.isPullback_right t).flip
  have ht' : IsPullback (CompatibleOpen.leftMap i (D.leftOpen t))
      ((i ⁻¹ᵁ D.leftOpen t).ι ≫ j) ((D.leftOpen t).ι ≫ D.left) D.right := by
    simpa only [D.inl_chart, CompatibleOpen.rightMap, Scheme.Hom.resLE_comp_ι] using ht
  let e := pullbackRestrictIsoRestrict i (D.leftOpen t)
  apply ht'.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← cancel_mono (D.leftOpen t).ι]
    simp [CompatibleOpen.leftMap, e, pullback.condition, Scheme.Cover.pullbackHom, leftOpenCover]
  · simp [e, leftOpenCover]
  · simp [leftOpenCover]
  · simp

end Langlands.AlgebraicGeometry.IntegralSchemePushout.CompatibleAffinePushoutAtlas
