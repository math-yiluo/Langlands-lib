import Langlands.Global.RealSplitTorusAdelicComparison
import Langlands.Global.AdelicSplitComponentIndependence
import Mathlib.GroupTheory.Subgroup.Center

/-! # Real identity-component images in rational ambient adelic groups -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme

namespace RationalRealAdelicPoints

variable {H G : GroupScheme (Spec (CommRingCat.of ℚ))}
variable [IsAffine H.X.left] [IsAffine G.X.left]

/-- Including the actual real points commutes with actual group-scheme maps. -/
theorem full_naturality (f : H ⟶ G) (x : Lie.AffinePoints H ℝ) :
    PositiveRealTorus.pointMap ℚ H G (Adeles ℚ) f (full H x) =
      full G (PositiveRealTorus.pointMap ℚ H G ℝ f x) := by
  apply (AdelicGroupPoints.split ℚ G).injective
  apply Prod.ext
  · change AdelicGroupPoints.infinite ℚ G _ = AdelicGroupPoints.infinite ℚ G _
    have hp : AdelicGroupPoints.infinite ℚ G
        (PositiveRealTorus.pointMap ℚ H G (Adeles ℚ) f (full H x)) =
        PositiveRealTorus.pointMap ℚ H G (InfiniteAdeles ℚ) f
          (AdelicGroupPoints.infinite ℚ H (full H x)) := by
      change Lie.affineMap G (AlgHom.fst ℚ (InfiniteAdeles ℚ) (FiniteAdeles ℚ))
          (PositiveRealTorus.pointMap ℚ H G (Adeles ℚ) f (full H x)) =
        PositiveRealTorus.pointMap ℚ H G (InfiniteAdeles ℚ) f
          (Lie.affineMap H (AlgHom.fst ℚ (InfiniteAdeles ℚ) (FiniteAdeles ℚ))
            (full H x))
      simp only [Lie.affineMap_apply, PositiveRealTorus.pointMap_apply, Category.assoc]
    rw [hp, infinite_full, infinite_full]
    change PositiveRealTorus.pointMap ℚ H G (InfiniteAdeles ℚ) f
        (Lie.affineMap H infiniteRealAlgebraMap x) =
      Lie.affineMap G infiniteRealAlgebraMap (PositiveRealTorus.pointMap ℚ H G ℝ f x)
    simp only [Lie.affineMap_apply, PositiveRealTorus.pointMap_apply, Category.assoc]
  · change AdelicGroupPoints.finite ℚ G _ = AdelicGroupPoints.finite ℚ G _
    have hp : AdelicGroupPoints.finite ℚ G
        (PositiveRealTorus.pointMap ℚ H G (Adeles ℚ) f (full H x)) =
        PositiveRealTorus.pointMap ℚ H G (FiniteAdeles ℚ) f
          (AdelicGroupPoints.finite ℚ H (full H x)) := by
      change Lie.affineMap G (AlgHom.snd ℚ (InfiniteAdeles ℚ) (FiniteAdeles ℚ))
          (PositiveRealTorus.pointMap ℚ H G (Adeles ℚ) f (full H x)) =
        PositiveRealTorus.pointMap ℚ H G (FiniteAdeles ℚ) f
          (Lie.affineMap H (AlgHom.snd ℚ (InfiniteAdeles ℚ) (FiniteAdeles ℚ))
            (full H x))
      simp only [Lie.affineMap_apply, PositiveRealTorus.pointMap_apply, Category.assoc]
    rw [hp, finite_full, finite_full, map_one]

end RationalRealAdelicPoints

namespace PositiveRealTorus

variable (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left]
variable (T : CommGroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine T.toGrp.X.left]
variable (i : T.toGrp ⟶ G)

local instance rationalSplitCenterAffinePointsTopology (H : GroupScheme (Spec (CommRingCat.of ℚ))) :
    TopologicalSpace (Lie.AffinePoints H ℝ) :=
  GroupScheme.affinePointsTopologicalSpace H (CommAlgCat.of ℚ ℝ)

/-- Map intrinsically positive actual real torus points into the ambient adelic group. -/
def ambientRealPositive :
    orderedCoefficientPositiveSubgroup ℚ T ℝ →ₜ* AdelicGroupPoints ℚ G :=
  (AdelicGroupPoints.map ℚ T.toGrp G i).comp (realToAdelic T)

omit [IsAffine G.X.left] in
@[simp] theorem ambientRealPositive_apply (a : orderedCoefficientPositiveSubgroup ℚ T ℝ) :
    ambientRealPositive G T i a =
      pointMap ℚ T.toGrp G (Adeles ℚ) i (RationalRealAdelicPoints.full T.toGrp a.val) := rfl

/-- The ambient map first applies the real scheme map and then includes real points. -/
theorem ambientRealPositive_eq_full (a : orderedCoefficientPositiveSubgroup ℚ T ℝ) :
    ambientRealPositive G T i a =
      RationalRealAdelicPoints.full G (pointMap ℚ T.toGrp G ℝ i a.val) :=
  RationalRealAdelicPoints.full_naturality i a.val

variable (I : Type) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of ℚ)) I)

omit [IsAffine G.X.left] in
include I e in
/-- The ambient real image is the existing intrinsic positive adelic image. -/
theorem range_ambientRealPositive :
    (ambientRealPositive G T i).toMonoidHom.range = imageSubgroup ℚ T G i := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨realToAdelic T a, ?_, rfl⟩
    rw [← range_realToAdelic T I e]
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [← range_realToAdelic T I e] at ha
    obtain ⟨x, rfl⟩ := ha
    exact ⟨x, rfl⟩

include I e in
/-- The real identity component gives exactly the same ambient adelic subset. -/
theorem ambient_full_image_connectedComponent_one :
    (fun a : Lie.AffinePoints T.toGrp ℝ =>
      RationalRealAdelicPoints.full G (pointMap ℚ T.toGrp G ℝ i a)) ''
        connectedComponent (1 : Lie.AffinePoints T.toGrp ℝ) =
      (imageSubgroup ℚ T G i : Set (AdelicGroupPoints ℚ G)) := by
  rw [connectedComponent_one_eq_orderedCoefficientPositiveSubgroup ℚ T I e ℝ]
  ext y
  constructor
  · rintro ⟨a, ha, h⟩
    rw [← range_ambientRealPositive G T i I e]
    exact ⟨⟨a, ha⟩, (ambientRealPositive_eq_full G T i ⟨a, ha⟩).trans h⟩
  · intro hy
    rw [← range_ambientRealPositive G T i I e] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a.val, a.property, (ambientRealPositive_eq_full G T i a).symm⟩

omit [IsAffine G.X.left] [IsAffine T.X.left] in
/-- Actual centrality makes the entire intrinsic positive image central on adelic points. -/
theorem imageSubgroup_le_center (hc : IsCentral i) :
    imageSubgroup ℚ T G i ≤ Subgroup.center (AdelicGroupPoints ℚ G) := by
  rintro y ⟨a, ha, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun x =>
    (commute_of_mem_center (hc _ a) x).eq.symm

omit [IsAffine G.X.left] in
include I e in
/-- The subgroup defining the existing quotient is generated by the actual real image
and the unchanged principal rational points. -/
theorem positiveRationalSubgroup_eq_realImage_sup :
    positiveRationalSubgroup ℚ G T i =
      (ambientRealPositive G T i).toMonoidHom.range ⊔
        AdelicGroupPoints.rationalSubgroup ℚ G := by
  rw [range_ambientRealPositive G T i I e]
  rfl

include I e in
/-- Centrality makes membership an actual real-positive-times-principal product.
No character-restriction injectivity or finite-index premise is needed. -/
theorem mem_positiveRationalSubgroup_iff_real (hc : IsCentral i)
    (x : AdelicGroupPoints ℚ G) :
    x ∈ positiveRationalSubgroup ℚ G T i ↔
      ∃ (a : Lie.AffinePoints T.toGrp ℝ), a ∈ connectedComponent 1 ∧
        ∃ q : RationalGroupPoints ℚ G,
          RationalRealAdelicPoints.full G (pointMap ℚ T.toGrp G ℝ i a) *
            AdelicGroupPoints.rational ℚ G q = x := by
  have : (imageSubgroup ℚ T G i).Normal :=
    Subgroup.normal_of_le_center (imageSubgroup_le_center G T i hc)
  change x ∈ imageSubgroup ℚ T G i ⊔ AdelicGroupPoints.rationalSubgroup ℚ G ↔ _
  rw [Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨a, ha, b, ⟨q, rfl⟩, h⟩
    have ha' : a ∈ (fun a : Lie.AffinePoints T.toGrp ℝ =>
        RationalRealAdelicPoints.full G (pointMap ℚ T.toGrp G ℝ i a)) ''
          connectedComponent 1 := by
      rwa [ambient_full_image_connectedComponent_one G T i I e]
    obtain ⟨r, hr, rfl⟩ := ha'
    exact ⟨r, hr, q, h⟩
  · rintro ⟨a, ha, q, rfl⟩
    refine ⟨_, ?_, _, ⟨q, rfl⟩, rfl⟩
    change _ ∈ (imageSubgroup ℚ T G i : Set (AdelicGroupPoints ℚ G))
    rw [← ambient_full_image_connectedComponent_one G T i I e]
    exact ⟨a, ha, rfl⟩

section Greatest

variable [LocallyOfFiniteType G.X.hom]
variable {T' : CommGroupScheme (Spec (CommRingCat.of ℚ))}
variable {i' : T'.toGrp ⟶ G}

omit [IsAffine T.X.left] in
/-- Every central split torus has its intrinsic adelic image contained in that of
a supplied split component, by actual finite-type factorization. -/
theorem imageSubgroup_le_of_centralSplitTorus (hi : IsSplitComponent i)
    (hi' : IsCentralSplitTorus i') :
    imageSubgroup ℚ T' G i' ≤ imageSubgroup ℚ T G i := by
  obtain ⟨f, hf⟩ := hi.exists_comp_eq (finiteType_coordinateAlgebra G) hi'
  exact imageSubgroup_le_of_factor ℚ G (Additive.ofMul f) hf

end Greatest

end PositiveRealTorus

end Langlands.Global
