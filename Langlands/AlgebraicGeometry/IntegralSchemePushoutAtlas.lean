import Langlands.AlgebraicGeometry.IntegralSchemePushoutAffineModel
import Langlands.AlgebraicGeometry.IntegralSchemePushoutAffineCover
import Langlands.AlgebraicGeometry.IntegralSchemePushoutDescent

/-! # The compatible affine atlas for integral scheme pushouts -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CompatibleOpen

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : i ⁻¹ᵁ U = j ⁻¹ᵁ V)

/-- Restricting the closed immersion to the common open preserves closedness. -/
instance leftMap_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (leftMap i U) := by
  rw [leftMap, Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The compatible source is the full inverse image of the right open. -/
lemma rightMap_isIntegral [IsIntegralHom j] :
    IsIntegralHom (rightMap i j U V hUV) := by
  have : IsIso (Z.homOfLE hUV.le) :=
    ⟨⟨Z.homOfLE hUV.ge, by simp, by simp⟩⟩
  exact inferInstanceAs (IsIntegralHom (Z.homOfLE hUV.le ≫ j ∣_ V))

end CompatibleOpen

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]

instance compatiblePairLeft_isAffine (p : CompatibleAffinePairs i j) :
    IsAffine p.left.1.toScheme := p.left.2

instance compatiblePairRight_isAffine (p : CompatibleAffinePairs i j) :
    IsAffine p.right.1.toScheme := p.right.2

instance compatiblePairSource_isAffine (p : CompatibleAffinePairs i j) :
    IsAffine (i ⁻¹ᵁ p.left.1).toScheme := p.left.2.preimage i

/-- The actual affine pushout atlas indexed by every compatible affine pair. -/
def compatibleAffinePushoutAtlas
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) :
    CompatibleAffinePushoutAtlas i j where
  Index := CompatibleAffinePairs i j
  leftOpen p := p.left.1
  rightOpen p := p.right.1
  compatible p := p.compatible
  covers_left x := by
    apply Opens.mem_iSup.mp
    rw [compatibleAffinePairs_cover_left i j hF]
    trivial
  covers_right y := by
    apply Opens.mem_iSup.mp
    rw [compatibleAffinePairs_cover_right i j hF]
    trivial
  model p := AffineSpan.model (CompatibleOpen.leftMap i p.left.1)
    (CompatibleOpen.rightMap i j p.left.1 p.right.1 p.compatible)
  affine _ := inferInstance
  inl p := AffineSpan.inl (CompatibleOpen.leftMap i p.left.1)
    (CompatibleOpen.rightMap i j p.left.1 p.right.1 p.compatible)
  inr p := AffineSpan.inr (CompatibleOpen.leftMap i p.left.1)
    (CompatibleOpen.rightMap i j p.left.1 p.right.1 p.compatible)
  isPushout p := AffineSpan.isPushout (CompatibleOpen.leftMap i p.left.1)
    (CompatibleOpen.rightMap i j p.left.1 p.right.1 p.compatible)

/-- Each left map in the atlas is integral. -/
lemma compatibleAffinePushoutAtlas_inl_isIntegral
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U)
    (p : CompatibleAffinePairs i j) :
    IsIntegralHom ((compatibleAffinePushoutAtlas i j hF).inl p) := by
  change IsIntegralHom (AffineSpan.inl (CompatibleOpen.leftMap i p.left.1)
    (CompatibleOpen.rightMap i j p.left.1 p.right.1 p.compatible))
  have := CompatibleOpen.rightMap_isIntegral i j p.left.1 p.right.1 p.compatible
  exact AffineSpan.inl_isIntegral _ _

/-- Each right map in the atlas is a closed immersion. -/
lemma compatibleAffinePushoutAtlas_inr_isClosedImmersion
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U)
    (p : CompatibleAffinePairs i j) :
    IsClosedImmersion ((compatibleAffinePushoutAtlas i j hF).inr p) := by
  change IsClosedImmersion (AffineSpan.inr (CompatibleOpen.leftMap i p.left.1)
    (CompatibleOpen.rightMap i j p.left.1 p.right.1 p.compatible))
  exact AffineSpan.inr_isClosedImmersion _ _

end Langlands.AlgebraicGeometry.IntegralSchemePushout
