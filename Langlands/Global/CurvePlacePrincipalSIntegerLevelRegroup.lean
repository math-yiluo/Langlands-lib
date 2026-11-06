import Langlands.Global.CurvePlacePrincipalSIntegerLevelWeil
import Langlands.Global.AdelicLevelModelTopologyProof

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerLevelWeil
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlacePrincipalSIntegerLevelRegroup

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open CurvePlacePrincipalSIntegerLevelWeil

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]

/-- Regroup an original upper place above a lower field/integer coordinate as its actual upper level coordinate. -/
def indexMap :
    (Σ i, Above k K L s t i) →
      CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))
  | ⟨.inl p, q⟩ => .inl ⟨q.1, by
      rw [mem_curvePlaceExceptionalPreimage, (curvePlaceRestriction_eq_iff q.1 p.1).mpr q.2]
      exact p.2⟩
  | ⟨.inr p, q⟩ => .inr ⟨q.1, by
      rw [mem_curvePlaceExceptionalPreimage, (curvePlaceRestriction_eq_iff q.1 p.1).mpr q.2]
      exact p.2⟩

/-- Restriction of the actual upper coordinate recovers its unique original lower coordinate. -/
def indexInv :
    CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))) →
        (Σ i, Above k K L s t i)
  | .inl q => ⟨.inl ⟨curvePlaceRestriction q.1,
      (mem_curvePlaceExceptionalPreimage _ q.1).mp q.2⟩, ⟨q.1, rfl⟩⟩
  | .inr q => ⟨.inr ⟨curvePlaceRestriction q.1, fun h =>
      q.2 ((mem_curvePlaceExceptionalPreimage _ q.1).mpr h)⟩, ⟨q.1, rfl⟩⟩

/-- The actual lower-coordinate/upper-place pairs are precisely all actual upper level coordinates. -/
def indexEquiv :
    (Σ i, Above k K L s t i) ≃
      CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))) where
  toFun := indexMap k K L s t
  invFun := indexInv k K L s t
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

variable
  (Y : Over (Spec (CommRingCat.of
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))

/-- Regrouping retains exactly the same original coefficient ring, scalar map and point topology. -/
def factorPointHomeomorph (z : Σ i, Above k K L s t i) :
    letI : TopologicalSpace (RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (upperFactor k K L s t z.1 z.2)) :=
      schemePointTopology _ Y (upperFactor k K L s t z.1 z.2)
    letI : TopologicalSpace (RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) (indexEquiv k K L s t z))) :=
      schemePointTopology _ Y _
    RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (upperFactor k K L s t z.1 z.2) ≃ₜ
      RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) (indexEquiv k K L s t z)) := by
  letI : TopologicalSpace (RingPoint
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (upperFactor k K L s t z.1 z.2)) :=
    schemePointTopology _ Y _
  letI : TopologicalSpace (RingPoint
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))) (indexEquiv k K L s t z))) :=
    schemePointTopology _ Y _
  rcases z with ⟨i, q⟩
  cases i <;> exact Homeomorph.refl _

/-- Regrouping all original upper point factors gives their original upper level coordinate product. -/
def productPointHomeomorph :
    letI : ∀ z : Σ i, Above k K L s t i, TopologicalSpace
        (RingPoint
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (upperFactor k K L s t z.1 z.2)) :=
      fun _ => schemePointTopology _ Y _
    letI : ∀ i : CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))), TopologicalSpace
        (RingPoint
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K))) i)) :=
      fun _ => schemePointTopology _ Y _
    (∀ z : Σ i, Above k K L s t i,
      RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (upperFactor k K L s t z.1 z.2)) ≃ₜ
      (∀ i : CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))),
        RingPoint
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K))) i)) := by
  letI : ∀ z : Σ i, Above k K L s t i, TopologicalSpace
      (RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (upperFactor k K L s t z.1 z.2)) :=
    fun z => schemePointTopology _ Y _
  letI : ∀ i : CurvePlaceLevelFactorIndex k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))), TopologicalSpace
      (RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) i)) :=
    fun i => schemePointTopology _ Y _
  exact (Homeomorph.piCongrRight (factorPointHomeomorph k K L s t Y)).trans
    (Homeomorph.piCongrLeft (Y := fun i => RingPoint
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))) i))
      (indexEquiv k K L s t))

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
@[simp]
theorem productPointHomeomorph_apply
    (x : ∀ z : Σ i, Above k K L s t i,
      RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (upperFactor k K L s t z.1 z.2)) (z : Σ i, Above k K L s t i) :
    productPointHomeomorph k K L s t Y x (indexEquiv k K L s t z) =
      factorPointHomeomorph k K L s t Y z (x z) := by
  simp only [productPointHomeomorph, Homeomorph.trans_apply,
    Homeomorph.piCongrLeft_apply_apply, Homeomorph.piCongrRight_apply]

variable [LocallyOfFiniteType Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)

/-- The actual lower Weil model and actual upper model have homeomorphic original adelic-level points. -/
def adelicLevelPointHomeomorph :
    letI : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (affineChartWeilRestriction
            (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
          (curvePlaceAdeleLevel k K (curvePlacePrincipalExceptional k K s (t : K)))) :=
      curvePlaceLevelModelPointTopology k K (curvePlacePrincipalExceptional k K s (t : K))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
    letI : TopologicalSpace (RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (curvePlaceAdeleLevel k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))))) :=
      curvePlaceLevelModelPointTopology k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y
    RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
        (curvePlaceAdeleLevel k K (curvePlacePrincipalExceptional k K s (t : K))) ≃ₜ
      RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (curvePlaceAdeleLevel k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) := by
  let R₀ := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let B₀ := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let S₀ := curvePlacePrincipalExceptional k K s (t : K)
  let T₀ := curvePlaceExceptionalPreimage (L := L) S₀
  let U₀ := CurvePlaceLevelFactor k L T₀
  let W := affineChartWeilRestriction R₀ B₀ Y
  letI : TopologicalSpace (RingPoint R₀ W (curvePlaceAdeleLevel k K S₀)) :=
    curvePlaceLevelModelPointTopology k K S₀ W
  letI : TopologicalSpace (RingPoint B₀ Y (curvePlaceAdeleLevel k L T₀)) :=
    curvePlaceLevelModelPointTopology k L T₀ Y
  letI : ∀ z : Σ i, Above k K L s t i,
      TopologicalSpace (RingPoint B₀ Y (upperFactor k K L s t z.1 z.2)) :=
    fun z => schemePointTopology _ Y _
  letI : ∀ i, TopologicalSpace (RingPoint B₀ Y (U₀ i)) :=
    fun i => schemePointTopology _ Y _
  letI : ∀ i, TopologicalSpace (RingPoint (U₀ i) (ringBaseChange B₀ (U₀ i) Y) (U₀ i)) :=
    fun i => schemePointTopology _ _ _
  letI : ∀ i, IsOpenUnits (U₀ i) := by
    intro i
    cases i <;> dsimp [U₀, CurvePlaceLevelFactor] <;> infer_instance
  let Hupper := IsHomeomorph.homeomorph (curvePlaceLevelModelPointMap k L T₀ Y)
    (curvePlaceLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated k L T₀ Y)
  exact (levelPointHomeomorph k K L s t Y n j hj).trans
    ((productPointHomeomorph k K L s t Y).trans
      ((Homeomorph.piCongrRight fun i =>
        schemePointBaseChangeHomeomorph B₀ (U₀ i) (U₀ i) Y).trans Hupper.symm))

/-- The original upper level coordinates are exactly the regrouped original local Weil components. -/
theorem adelicLevelPointHomeomorph_coordinates
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
      (curvePlaceAdeleLevel k K (curvePlacePrincipalExceptional k K s (t : K)))) :
    curvePlaceLevelModelPointMap k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        Y (adelicLevelPointHomeomorph k K L s t Y n j hj p) =
      fun i => ringPointBaseChangeEquiv
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))))
        (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) i)
        (CurvePlaceLevelFactor k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) i) Y
        (productPointHomeomorph k K L s t Y
          (levelPointHomeomorph k K L s t Y n j hj p) i) := by
  let B₀ := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let T₀ := curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K))
  let U₀ := CurvePlaceLevelFactor k L T₀
  let : TopologicalSpace (RingPoint B₀ Y (curvePlaceAdeleLevel k L T₀)) :=
    curvePlaceLevelModelPointTopology k L T₀ Y
  let : ∀ z : Σ i, Above k K L s t i,
      TopologicalSpace (RingPoint B₀ Y (upperFactor k K L s t z.1 z.2)) :=
    fun z => schemePointTopology _ Y _
  let : ∀ i, TopologicalSpace (RingPoint B₀ Y (U₀ i)) :=
    fun i => schemePointTopology _ Y _
  let : ∀ i, TopologicalSpace (RingPoint (U₀ i) (ringBaseChange B₀ (U₀ i) Y) (U₀ i)) :=
    fun i => schemePointTopology _ _ _
  let : ∀ i, IsOpenUnits (U₀ i) := by
    intro i
    cases i <;> dsimp [U₀, CurvePlaceLevelFactor] <;> infer_instance
  let Hupper := IsHomeomorph.homeomorph (curvePlaceLevelModelPointMap k L T₀ Y)
    (curvePlaceLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated k L T₀ Y)
  let Hlocal := Homeomorph.piCongrRight fun i =>
    schemePointBaseChangeHomeomorph B₀ (U₀ i) (U₀ i) Y
  exact Hupper.apply_symm_apply
    (Hlocal (productPointHomeomorph k K L s t Y (levelPointHomeomorph k K L s t Y n j hj p)))

end Langlands.Global.CurvePlacePrincipalSIntegerLevelRegroup
