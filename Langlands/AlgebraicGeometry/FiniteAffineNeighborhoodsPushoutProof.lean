import Langlands.AlgebraicGeometry.FiniteAffineNeighborhoodsPinchingAux
import Langlands.AlgebraicGeometry.FiniteAffineNeighborhoodsPushoutCharts
import Langlands.AlgebraicGeometry.IntegralSchemePushoutAtlas

/-! # Finite pinching preserves finite-set affine neighborhoods -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The model pushout built from the compatible affine atlas has an affine
chart containing each compatible affine pair. -/
theorem FinitePinching.hasAffineCharts_compatibleAffinePushoutAtlas
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) :
    FinitePinching.HasAffineCharts i j
      (IntegralSchemePushout.compatibleAffinePushoutAtlas i j hF).left
      (IntegralSchemePushout.compatibleAffinePushoutAtlas i j hF).right := by
  intro U V hUV
  let D := IntegralSchemePushout.compatibleAffinePushoutAtlas i j hF
  let t : D.Index := ⟨(U, V), hUV⟩
  exact ⟨⟨(D.chart t).opensRange, isAffineOpen_opensRange _⟩,
    (D.chart_preimage_left t).ge, (D.chart_preimage_right t).ge⟩

/-- Ferrand's Theorem 5.4: the pushout of a closed immersion and a finite
morphism of schemes with finite-set affine neighborhoods again has finite-set
affine neighborhoods. -/
theorem finiteAffineNeighborhoodsPushout :
    FiniteAffineNeighborhoodsPushoutStatement.{u} := by
  intro X Y Z P i j a b hi hj hX hY h
  let hF := FinitePinching.exists_affineOpen_fibre i j hX
  let D := IntegralSchemePushout.compatibleAffinePushoutAtlas i j hF
  have : IsIntegralHom D.left := D.left_isIntegral
    (IntegralSchemePushout.compatibleAffinePushoutAtlas_inl_isIntegral i j hF)
  have : IsClosedImmersion D.right := D.right_isClosedImmersion
    (IntegralSchemePushout.compatibleAffinePushoutAtlas_inr_isClosedImmersion i j hF)
  exact FinitePinching.hasFiniteAffineNeighborhoods_of_model
    (fun E F hE hF hEZ => exists_compatible_affineOpens_of_finite i j hX hY E F hE hF hEZ)
    D.isPushout_global
    (FinitePinching.hasAffineCharts_compatibleAffinePushoutAtlas i j hF) h

end Langlands.AlgebraicGeometry
