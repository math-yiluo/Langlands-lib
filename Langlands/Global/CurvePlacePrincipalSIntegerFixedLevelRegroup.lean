import Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.FixedModelLocalProduct
  Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelRegroup

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open CurvePlacePrincipalSIntegerFixedLevelWeil

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))

/-- Full preimage of the enlarged lower support, containing the original upper support. -/
def upperLevel : AdelicLevelIndexAbove (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K))) :=
  ⟨curvePlaceExceptionalPreimage (L := L) T.val, fun q hq =>
    (mem_curvePlaceExceptionalPreimage T.val q).mpr
      (T.property ((mem_curvePlaceExceptionalPreimage _ q).mp hq))⟩

/-- Regroup each original upper place above an enlarged lower coordinate. -/
def indexMap : (Σ i, Above k K L s t T i) →
    CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L) T.val)
  | ⟨.inl p, q⟩ => .inl ⟨q.1, by
      rw [mem_curvePlaceExceptionalPreimage, (curvePlaceRestriction_eq_iff q.1 p.1).mpr q.2]
      exact p.2⟩
  | ⟨.inr p, q⟩ => .inr ⟨q.1, by
      rw [mem_curvePlaceExceptionalPreimage, (curvePlaceRestriction_eq_iff q.1 p.1).mpr q.2]
      exact p.2⟩

/-- Restrict an original upper place to recover its unique enlarged lower coordinate. -/
def indexInv :
    CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L) T.val) →
      (Σ i, Above k K L s t T i)
  | .inl q => ⟨.inl ⟨curvePlaceRestriction q.1,
      (mem_curvePlaceExceptionalPreimage _ q.1).mp q.2⟩, ⟨q.1, rfl⟩⟩
  | .inr q => ⟨.inr ⟨curvePlaceRestriction q.1, fun h =>
      q.2 ((mem_curvePlaceExceptionalPreimage _ q.1).mpr h)⟩, ⟨q.1, rfl⟩⟩

/-- All original paired local factors are precisely the original enlarged upper coordinates. -/
def indexEquiv : (Σ i, Above k K L s t T i) ≃
    CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L) T.val) where
  toFun := indexMap k K L s t T
  invFun := indexInv k K L s t T
  left_inv z := by
    rcases z with ⟨i, q⟩
    cases i with
    | inl p =>
      rcases p with ⟨p, hp⟩
      rcases q with ⟨q, hq⟩
      have h : curvePlaceRestriction q = p := (curvePlaceRestriction_eq_iff q p).mpr hq
      cases h
      rfl
    | inr p =>
      rcases p with ⟨p, hp⟩
      rcases q with ⟨q, hq⟩
      have h : curvePlaceRestriction q = p := (curvePlaceRestriction_eq_iff q p).mpr hq
      cases h
      rfl
  right_inv z := by cases z <;> rfl

variable (Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))

/-- Each regrouped factor has the same original ring, fixed coefficient action and point topology. -/
def factorPointHomeomorph (z : Σ i, Above k K L s t T i) :
    letI := schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)
    letI := schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val (indexEquiv k K L s t T z))
    RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2) ≃ₜ
      RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val (indexEquiv k K L s t T z)) := by
  letI := schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)
  letI := schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
    (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val (indexEquiv k K L s t T z))
  rcases z with ⟨i, q⟩
  cases i with
  | inl p =>
    have h : FixedModelLocalProduct.curveFactorAlgebra k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        (upperLevel k K L s t T) (indexEquiv k K L s t T ⟨.inl p, q⟩) =
        CurvePlacePrincipalSIntegerFixedLevelWeil.upperCoefficientAlgebra k K L s t T (.inl p) q :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact Homeomorph.refl _
  | inr p =>
    have h : FixedModelLocalProduct.curveFactorAlgebra k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        (upperLevel k K L s t T) (indexEquiv k K L s t T ⟨.inr p, q⟩) =
        CurvePlacePrincipalSIntegerFixedLevelWeil.upperCoefficientAlgebra k K L s t T (.inr p) q :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact Homeomorph.refl _

/-- Regroup the original upper factors with their original fixed-base product topologies. -/
def productPointHomeomorph :
    letI : ∀ z : Σ i, Above k K L s t T i,
        TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)) :=
      fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
    letI : ∀ i, TopologicalSpace
        (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) :=
      fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
    (∀ z : Σ i, Above k K L s t T i, RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)) ≃ₜ
      (∀ i, RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) := by
  letI : ∀ z : Σ i, Above k K L s t T i,
      TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  letI : ∀ i, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  exact (Homeomorph.piCongrRight (factorPointHomeomorph k K L s t T Y)).trans
    (Homeomorph.piCongrLeft (Y := fun i =>
      RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i))
      (indexEquiv k K L s t T))

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
@[simp]
theorem productPointHomeomorph_apply
    (x : ∀ z : Σ i, Above k K L s t T i, RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2))
    (z : Σ i, Above k K L s t T i) :
    productPointHomeomorph k K L s t T Y x (indexEquiv k K L s t T z) =
      factorPointHomeomorph k K L s t T Y z (x z) := by
  let : ∀ z : Σ i, Above k K L s t T i,
      TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  let : ∀ i, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  change (Homeomorph.piCongrLeft (Y := fun i =>
    RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) (indexEquiv k K L s t T))
    ((Homeomorph.piCongrRight (factorPointHomeomorph k K L s t T Y)) x)
    (indexEquiv k K L s t T z) = _
  exact Homeomorph.piCongrLeft_apply_apply (Y := fun i =>
    RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i))
    (indexEquiv k K L s t T) ((Homeomorph.piCongrRight (factorPointHomeomorph k K L s t T Y)) x) z

variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

/-- Original upper enlarged-level points are homeomorphic to their original fixed-base coordinates. -/
def upperPointHomeomorph :
    letI := curvePlaceFixedModelStageTopology k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y (upperLevel k K L s t T)
    letI : ∀ i, TopologicalSpace
        (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) :=
      fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
    RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceAdeleLevelOver k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T)) ≃ₜ
      (∀ i, RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) := by
  let U := CurvePlaceLevelFactor k L (upperLevel k K L s t T).val
  letI := curvePlaceFixedModelStageTopology k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y (upperLevel k K L s t T)
  letI := localProductPointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) U Y
  letI : ∀ i, TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (U i)) := fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  let E := Equiv.ofBijective (productPointMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) U Y)
    ⟨productPointMap_injective (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) U Y, productPointMap_surjective (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) U Y⟩
  exact (FixedModelLocalProduct.curveStageHomeomorph k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) Y).trans
      (E.toHomeomorphOfIsInducing
        (productPointMap_isInducing_localProductPointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) U Y))

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- The original upper coordinate map is the literal enlarged-level projection. -/
theorem upperPointHomeomorph_coordinate
    (p : RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceAdeleLevelOver k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T)))
    (i : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val) :
    (upperPointHomeomorph k K L s t T Y p i).left =
      Spec.map (CommRingCat.ofHom
        (curvePlaceLevelFactorProjection k L (upperLevel k K L s t T).val i)) ≫ p.left :=
  FixedModelLocalProduct.curveStageHomeomorph_coordinate k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) Y p i

variable [LocallyOfFiniteType Y.hom] (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)

/-- The two original fixed integral models have homeomorphic points at every enlarged full-preimage level. -/
def adelicLevelPointHomeomorph :
    letI := curvePlaceFixedModelStageTopology k K (curvePlacePrincipalExceptional k K s (t : K)) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) T
    letI := curvePlaceFixedModelStageTopology k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y (upperLevel k K L s t T)
    RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) ≃ₜ
      RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceAdeleLevelOver k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T)) := by
  letI := curvePlaceFixedModelStageTopology k K (curvePlacePrincipalExceptional k K s (t : K)) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) T
  letI := curvePlaceFixedModelStageTopology k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y (upperLevel k K L s t T)
  letI : ∀ z : Σ i, Above k K L s t T i,
      TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  letI : ∀ i, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  exact (CurvePlacePrincipalSIntegerFixedLevelWeil.levelPointHomeomorph k K L s t T Y n j hj).trans
    ((productPointHomeomorph k K L s t T Y).trans (upperPointHomeomorph k K L s t T Y).symm)

/-- All original upper coordinates are exactly the regrouped original local Weil components. -/
theorem adelicLevelPointHomeomorph_coordinates
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    upperPointHomeomorph k K L s t T Y (adelicLevelPointHomeomorph k K L s t T Y n j hj p) =
      productPointHomeomorph k K L s t T Y
        (CurvePlacePrincipalSIntegerFixedLevelWeil.levelPointHomeomorph k K L s t T Y n j hj p) := by
  let := curvePlaceFixedModelStageTopology k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y (upperLevel k K L s t T)
  let : ∀ z : Σ i, Above k K L s t T i,
      TopologicalSpace (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (upperFactor k K L s t T z.1 z.2)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  let : ∀ i, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val i)) :=
    fun _ => schemePointTopology (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y _
  exact (upperPointHomeomorph k K L s t T Y).apply_symm_apply _

/-- Each literal original upper projection recovers its original regrouped local Weil point. -/
theorem adelicLevelPointHomeomorph_coordinate_left
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (z : Σ i, Above k K L s t T i) :
    Spec.map (CommRingCat.ofHom (curvePlaceLevelFactorProjection k L
        (upperLevel k K L s t T).val (indexEquiv k K L s t T z))) ≫
        (adelicLevelPointHomeomorph k K L s t T Y n j hj p).left =
      (factorPointHomeomorph k K L s t T Y z
        (CurvePlacePrincipalSIntegerFixedLevelWeil.levelPointHomeomorph k K L s t T Y n j hj p z)).left := by
  rw [← upperPointHomeomorph_coordinate]
  rw [adelicLevelPointHomeomorph_coordinates, productPointHomeomorph_apply]

end Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelRegroup
