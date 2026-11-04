import Langlands.Global.RationalSplitCenterRealImage
import Langlands.Global.AdelicPositiveImageClosed

/-! # Closed ambient real identity-component images -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

variable (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left]
variable (T : CommGroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine T.X.left]
variable (i : T.toGrp ⟶ G) [IsClosedImmersion i.hom.hom.left]
variable (I : Type) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of ℚ)) I)

local instance rationalRealClosedAffinePointsTopology
    (H : GroupScheme (Spec (CommRingCat.of ℚ))) :
    TopologicalSpace (Lie.AffinePoints H ℝ) :=
  GroupScheme.affinePointsTopologicalSpace H (CommAlgCat.of ℚ ℝ)

include I e in
/-- A supplied actual closed immersion gives a closed embedding of the actual
positive real points into the ambient adelic group. -/
theorem isClosedEmbedding_ambientRealPositive :
    IsClosedEmbedding (ambientRealPositive G T i) :=
  (AdelicGroupPoints.isClosedEmbedding_map ℚ T.toGrp G i).comp
    (isClosedEmbedding_realToAdelic T I e)

include I e in
/-- The ambient image of the actual real identity component is closed. -/
theorem isClosed_ambient_full_image_connectedComponent_one :
    IsClosed ((fun a : Lie.AffinePoints T.toGrp ℝ =>
      RationalRealAdelicPoints.full G (pointMap ℚ T.toGrp G ℝ i a)) ''
        connectedComponent (1 : Lie.AffinePoints T.toGrp ℝ)) := by
  rw [ambient_full_image_connectedComponent_one G T i I e]
  exact isClosed_imageSubgroup ℚ G T i

/-- Actual positive real points are continuously isomorphic to the existing
ambient closed image subgroup. -/
def ambientRealPositiveEquiv :
    orderedCoefficientPositiveSubgroup ℚ T ℝ ≃ₜ* closedImageSubgroup ℚ G T i := by
  let f : orderedCoefficientPositiveSubgroup ℚ T ℝ →* closedImageSubgroup ℚ G T i :=
    (ambientRealPositive G T i).toMonoidHom.codRestrict (imageSubgroup ℚ T G i)
      (fun a => by
        rw [← range_ambientRealPositive G T i I e]
        exact ⟨a, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact (isClosedEmbedding_ambientRealPositive G T i I e).injective
        (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      change y ∈ imageSubgroup ℚ T G i at hy
      rw [← range_ambientRealPositive G T i I e] at hy
      obtain ⟨a, ha⟩ := hy
      exact ⟨a, Subtype.ext ha⟩
  let m := MulEquiv.ofBijective f hf
  refine
    { m with
      continuous_toFun := (ambientRealPositive G T i).continuous.subtype_mk _
      continuous_invFun := ?_ }
  apply (isClosedEmbedding_ambientRealPositive G T i I e).isEmbedding.isInducing.continuous_iff.mpr
  have hcomp : (fun y => ambientRealPositive G T i (m.symm y)) = Subtype.val := by
    funext y
    exact congrArg Subtype.val (m.apply_symm_apply y)
  change Continuous (fun y => ambientRealPositive G T i (m.symm y))
  rw [hcomp]
  exact continuous_subtype_val

@[simp] theorem ambientRealPositiveEquiv_apply
    (a : orderedCoefficientPositiveSubgroup ℚ T ℝ) :
    (ambientRealPositiveEquiv G T i I e a : AdelicGroupPoints ℚ G) =
      ambientRealPositive G T i a := rfl

/-- The equivalence uses the actual real point map and finite identity insertion. -/
theorem ambientRealPositiveEquiv_apply_eq_full
    (a : orderedCoefficientPositiveSubgroup ℚ T ℝ) :
    (ambientRealPositiveEquiv G T i I e a : AdelicGroupPoints ℚ G) =
      RationalRealAdelicPoints.full G (pointMap ℚ T.toGrp G ℝ i a.val) :=
  ambientRealPositive_eq_full G T i a

@[simp] theorem ambientRealPositiveEquiv_symm_apply
    (y : closedImageSubgroup ℚ G T i) :
    ambientRealPositive G T i ((ambientRealPositiveEquiv G T i I e).symm y) = y :=
  congrArg Subtype.val ((ambientRealPositiveEquiv G T i I e).apply_symm_apply y)

end Langlands.Global.PositiveRealTorus
