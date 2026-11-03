import Langlands.Global.RealSplitTorusPositiveParameters
import Langlands.Global.AdelicGroupProduct
import Langlands.GroupScheme.Torus.CocharacterDatum

/-! # The actual real-to-adelic map on rational split tori -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global

open Langlands.GroupScheme

namespace RationalRealAdelicPoints

/-- The actual real coefficient map into the rational infinite adeles. -/
def infiniteRealAlgebraMap : ℝ →ₐ[ℚ] InfiniteAdeles ℚ :=
  (PositiveRealIdeles.infiniteRealEmbedding ℚ).toRatAlgHom

variable (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left]

local instance (H : GroupScheme (Spec (CommRingCat.of ℚ))) :
    TopologicalSpace (Lie.AffinePoints H ℝ) :=
  GroupScheme.affinePointsTopologicalSpace H (CommAlgCat.of ℚ ℝ)

/-- Real points extended along the actual rational infinite coefficient map. -/
def infinite : Lie.AffinePoints G ℝ →ₜ* InfiniteAdelicGroupPoints ℚ G where
  toMonoidHom := Lie.affineMap G infiniteRealAlgebraMap
  continuous_toFun := G.continuous_affinePointMap
    (CommAlgCat.ofHom infiniteRealAlgebraMap)
    (PositiveRealIdeles.continuous_infiniteRealEmbedding ℚ)

/-- Include actual real points with the finite adelic point equal to the identity. -/
def full : Lie.AffinePoints G ℝ →ₜ* AdelicGroupPoints ℚ G :=
  (AdelicGroupPoints.ofInfinite ℚ G).comp (infinite G)

@[simp] theorem infinite_full (x : Lie.AffinePoints G ℝ) :
    AdelicGroupPoints.infinite ℚ G (full G x) = infinite G x :=
  AdelicGroupPoints.infinite_ofInfinite ℚ G _

@[simp] theorem finite_full (x : Lie.AffinePoints G ℝ) :
    AdelicGroupPoints.finite ℚ G (full G x) = 1 :=
  AdelicGroupPoints.finite_ofInfinite ℚ G _

end RationalRealAdelicPoints

namespace PositiveRealTorus

section CoefficientNaturality

universe u

variable (F : Type u) [Field F]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable {A B : Type u} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]

/-- The genuine splitting coordinates commute with extension of coefficients. -/
theorem coordinates_affineMap (f : A →ₐ[F] B) (x : Lie.AffinePoints T.toGrp A) :
    coordinates F I T e B (Lie.affineMap T.toGrp f x) =
      fun i => Units.map f.toMonoidHom (coordinates F I T e A x i) := by
  funext i
  rw [← characterValue_coordinateCharacter,
    CocharacterDatum.characterValue_affineMap, characterValue_coordinateCharacter]

end CoefficientNaturality

section RationalTorus

variable (T : CommGroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine T.toGrp.X.left]
variable (I : Type) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of ℚ)) I)

local instance (H : GroupScheme (Spec (CommRingCat.of ℚ))) :
    TopologicalSpace (Lie.AffinePoints H ℝ) :=
  GroupScheme.affinePointsTopologicalSpace H (CommAlgCat.of ℚ ℝ)

/-- On positive parameters, the actual real-point inclusion is the scalar adelic map. -/
theorem rationalRealFull_orderedCoefficientFull (x : I → ℝ≥0ˣ) :
    RationalRealAdelicPoints.full T.toGrp (orderedCoefficientFull ℚ T ℝ I e x) =
      full ℚ I T e x := by
  apply (AdelicGroupPoints.split ℚ T.toGrp).injective
  apply Prod.ext
  · change AdelicGroupPoints.infinite ℚ T.toGrp _ =
      AdelicGroupPoints.infinite ℚ T.toGrp _
    rw [RationalRealAdelicPoints.infinite_full]
    apply (coordinates ℚ I T e (InfiniteAdeles ℚ)).injective
    funext i
    let f : Adeles ℚ →ₐ[ℚ] InfiniteAdeles ℚ :=
      AlgHom.fst ℚ (InfiniteAdeles ℚ) (FiniteAdeles ℚ)
    have hr := congrFun (coordinates_affineMap ℚ T I e
      RationalRealAdelicPoints.infiniteRealAlgebraMap
      (orderedCoefficientFull ℚ T ℝ I e x)) i
    have hp := congrFun (coordinates_affineMap ℚ T I e f (full ℚ I T e x)) i
    have hx := congrFun (coordinates_orderedCoefficientFull ℚ T ℝ I e x) i
    have hy := congrFun (coordinates_full ℚ I T e x) i
    calc
      _ = Units.map RationalRealAdelicPoints.infiniteRealAlgebraMap.toMonoidHom
          (coordinates ℚ I T e ℝ (orderedCoefficientFull ℚ T ℝ I e x) i) := hr
      _ = Units.map RationalRealAdelicPoints.infiniteRealAlgebraMap.toMonoidHom
          (positiveUnitMap ℝ (x i)) :=
        congrArg (Units.map RationalRealAdelicPoints.infiniteRealAlgebraMap.toMonoidHom) hx
      _ = Units.map f.toMonoidHom (PositiveRealIdeles.full ℚ (x i)) := by
        apply Units.ext
        rfl
      _ = _ := (congrArg (Units.map f.toMonoidHom) hy).symm.trans hp.symm
  · change AdelicGroupPoints.finite ℚ T.toGrp _ =
      AdelicGroupPoints.finite ℚ T.toGrp _
    rw [RationalRealAdelicPoints.finite_full]
    apply (coordinates ℚ I T e (FiniteAdeles ℚ)).injective
    funext i
    let f : Adeles ℚ →ₐ[ℚ] FiniteAdeles ℚ :=
      AlgHom.snd ℚ (InfiniteAdeles ℚ) (FiniteAdeles ℚ)
    have hp := congrFun (coordinates_affineMap ℚ T I e f (full ℚ I T e x)) i
    have hy := congrFun (coordinates_full ℚ I T e x) i
    calc
      coordinates ℚ I T e (FiniteAdeles ℚ) 1 i = 1 :=
        congrFun ((coordinates ℚ I T e (FiniteAdeles ℚ)).map_one) i
      _ = Units.map f.toMonoidHom (PositiveRealIdeles.full ℚ (x i)) := by
        apply Units.ext
        rfl
      _ = coordinates ℚ I T e (FiniteAdeles ℚ)
          (AdelicGroupPoints.finite ℚ T.toGrp (full ℚ I T e x)) i :=
        (congrArg (Units.map f.toMonoidHom) hy).symm.trans hp.symm

/-- The canonical actual real-to-adelic map restricted to intrinsic positive points. -/
def realToAdelic :
    orderedCoefficientPositiveSubgroup ℚ T ℝ →ₜ* Lie.AffinePoints T.toGrp (Adeles ℚ) where
  toMonoidHom := (RationalRealAdelicPoints.full T.toGrp).toMonoidHom.comp
    (orderedCoefficientPositiveSubgroup ℚ T ℝ).subtype
  continuous_toFun := (RationalRealAdelicPoints.full T.toGrp).continuous.comp
    continuous_subtype_val

@[simp] theorem realToAdelic_apply
    (x : orderedCoefficientPositiveSubgroup ℚ T ℝ) :
    realToAdelic T x = RationalRealAdelicPoints.full T.toGrp x.val := rfl

@[simp] theorem realToAdelic_parameter (x : I → ℝ≥0ˣ) :
    realToAdelic T (orderedCoefficientParameterEquiv ℚ T ℝ I e x) =
      full ℚ I T e x :=
  rationalRealFull_orderedCoefficientFull T I e x

/-- The canonical map is the known scalar map after reading the actual real parameters. -/
theorem realToAdelic_eq_full_parameters
    (x : orderedCoefficientPositiveSubgroup ℚ T ℝ) :
    realToAdelic T x =
      full ℚ I T e ((orderedCoefficientParameterEquiv ℚ T ℝ I e).symm x) := by
  rw [← realToAdelic_parameter T I e]
  rw [ContinuousMulEquiv.apply_symm_apply]

include I e in
/-- The actual image is exactly the intrinsic positive scalar adelic subgroup. -/
theorem range_realToAdelic :
    (realToAdelic T).toMonoidHom.range = intrinsicSubgroup ℚ T := by
  rw [← subgroup_eq_intrinsicSubgroup ℚ I T e]
  apply Subgroup.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(orderedCoefficientParameterEquiv ℚ T ℝ I e).symm x,
      (realToAdelic_eq_full_parameters T I e x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨orderedCoefficientParameterEquiv ℚ T ℝ I e x,
      realToAdelic_parameter T I e x⟩

include I e in
/-- The real identity-component map is a closed embedding in the actual adelic topology. -/
theorem isClosedEmbedding_realToAdelic : IsClosedEmbedding (realToAdelic T) := by
  have heq : (realToAdelic T : _ → _) =
      fun x => full ℚ I T e ((orderedCoefficientParameterEquiv ℚ T ℝ I e).symm x) :=
    funext (realToAdelic_eq_full_parameters T I e)
  rw [heq]
  exact (isClosedEmbedding_full ℚ I T e).comp
    (orderedCoefficientParameterEquiv ℚ T ℝ I e).symm.toHomeomorph.isClosedEmbedding

include I e in
/-- The actual real identity component has exactly the intrinsic positive adelic image. -/
theorem full_image_connectedComponent_one :
    RationalRealAdelicPoints.full T.toGrp ''
        connectedComponent (1 : Lie.AffinePoints T.toGrp ℝ) =
      (intrinsicSubgroup ℚ T : Set (Lie.AffinePoints T.toGrp (Adeles ℚ))) := by
  rw [connectedComponent_one_eq_orderedCoefficientPositiveSubgroup ℚ T I e ℝ]
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hr : y ∈ (realToAdelic T).toMonoidHom.range := ⟨⟨x, hx⟩, hxy⟩
    rwa [range_realToAdelic T I e] at hr
  · intro hy
    rw [← range_realToAdelic T I e] at hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨x.val, x.property, rfl⟩

end RationalTorus

end PositiveRealTorus

end Langlands.Global
