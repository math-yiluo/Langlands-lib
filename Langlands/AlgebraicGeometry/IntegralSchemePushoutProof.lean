import Langlands.AlgebraicGeometry.IntegralSchemePushoutAtlas
import Langlands.AlgebraicGeometry.IntegralSchemePushoutAffineCartesian
import Langlands.AlgebraicGeometry.IntegralSchemePushoutStatement

/-! # Scheme pushouts along closed immersions and integral maps -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace IntegralSchemePushout.AffineSpan

/-- The affine model square is cartesian. -/
lemma isPullback {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsClosedImmersion i] :
    IsPullback i j (inl i j) (inr i j) := by
  have h := isPullback_specMap_pullback i.appTop j.appTop
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  apply h.of_iso' Z.isoSpec X.isoSpec Y.isoSpec (Iso.refl _)
  · exact Scheme.isoSpec_hom_naturality i
  · exact Scheme.isoSpec_hom_naturality j
  · change inl i j = inl i j ≫ 𝟙 _
    rw [Category.comp_id]
  · change inr i j = inr i j ≫ 𝟙 _
    rw [Category.comp_id]

end IntegralSchemePushout.AffineSpan

/-- A closed immersion and an integral map admit the stated scheme pushout. -/
theorem integralSchemePushout : IntegralSchemePushoutStatement.{u} := by
  intro X Y Z i j hi hj hF
  let := hi
  let := hj
  let D := IntegralSchemePushout.compatibleAffinePushoutAtlas i j hF
  refine ⟨D.scheme, D.left, D.right, D.isPushout_global, ?_, ?_, ?_⟩
  · apply D.isPullback_global
    intro p
    change IsPullback (IntegralSchemePushout.CompatibleOpen.leftMap i p.left.1)
      (IntegralSchemePushout.CompatibleOpen.rightMap i j p.left.1 p.right.1 p.compatible)
      (IntegralSchemePushout.AffineSpan.inl _ _)
      (IntegralSchemePushout.AffineSpan.inr _ _)
    exact IntegralSchemePushout.AffineSpan.isPullback _ _
  · exact D.left_isIntegral
      (IntegralSchemePushout.compatibleAffinePushoutAtlas_inl_isIntegral i j hF)
  · exact D.right_isClosedImmersion
      (IntegralSchemePushout.compatibleAffinePushoutAtlas_inr_isClosedImmersion i j hF)

end Langlands.AlgebraicGeometry
