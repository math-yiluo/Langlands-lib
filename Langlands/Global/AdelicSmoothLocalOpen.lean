import Langlands.Global.AdelicSmoothLocalOpenStatement
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Smooth openness in the original local factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- Smoothness is preserved by the actual scheme base-change functor. -/
theorem smooth_ringBaseChangeMap
    (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y) [Smooth f.left] :
    Smooth ((Over.pullback (Spec.algebraMap C D)).map f).left := by
  exact MorphismProperty.overPullbackMap (P := @Smooth)
    (Spec.algebraMap C D) f inferInstance

/-- Complete-field smooth openness retains an arbitrary original coefficient base. -/
theorem isOpenMap_completeFieldCoefficientSmoothPointMap
    (C K : Type u) [CommRing C] [NontriviallyNormedField K] [CompleteSpace K]
    [Algebra C K] {X Y : Over (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) [Smooth f.left] :
    @IsOpenMap _ _ (schemePointTopology C X K) (schemePointTopology C Y K)
      (fun p : RingPoint C X K => p ≫ f) := by
  let : TopologicalSpace (RingPoint C X K) := schemePointTopology C X K
  let : TopologicalSpace (RingPoint C Y K) := schemePointTopology C Y K
  let : TopologicalSpace (RingPoint K (ringBaseChange C K X) K) :=
    schemePointTopology K (ringBaseChange C K X) K
  let : TopologicalSpace (RingPoint K (ringBaseChange C K Y) K) :=
    schemePointTopology K (ringBaseChange C K Y) K
  let F : ringBaseChange C K X ⟶ ringBaseChange C K Y :=
    (Over.pullback (Spec.algebraMap C K)).map f
  let : Smooth F.left := smooth_ringBaseChangeMap C K f
  let eX := schemePointBaseChangeHomeomorph C K K X
  let eY := schemePointBaseChangeHomeomorph C K K Y
  have heq : (fun p : RingPoint C X K => p ≫ f) =
      eY.symm ∘ (fun p : RingPoint K (ringBaseChange C K X) K => p ≫ F) ∘ eX := by
    funext p
    apply eY.injective
    dsimp only [Function.comp_apply]
    rw [Homeomorph.apply_symm_apply]
    exact ringPointBaseChangeEquiv_natural C K K f p
  rw [heq]
  exact eY.symm.isOpenMap.comp
    ((isOpenMap_smoothSchemePointMap K F).comp eX.isOpenMap)

/-- Open coefficient embeddings restrict complete-field smooth openness to
integral points, preserving the original model and coefficient actions. -/
theorem isOpenMap_integralCoefficientSmoothPointMap
    (C R K : Type u) [CommRing C] [CommRing R] [_root_.IsReduced R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [NontriviallyNormedField K] [CompleteSpace K]
    [Algebra C R] [Algebra C K]
    {X Y : Over (Spec (CommRingCat.of C))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [Smooth f.left] (j : R →ₐ[C] K) (hj : IsOpenEmbedding j) :
    @IsOpenMap _ _ (schemePointTopology C X R) (schemePointTopology C Y R)
      (fun p : RingPoint C X R => p ≫ f) := by
  let : TopologicalSpace (RingPoint C X R) := schemePointTopology C X R
  let : TopologicalSpace (RingPoint C Y R) := schemePointTopology C Y R
  let : TopologicalSpace (RingPoint C X K) := schemePointTopology C X K
  let : TopologicalSpace (RingPoint C Y K) := schemePointTopology C Y K
  let eX := RingPoint.changeRing (X := X) j
  let eY := RingPoint.changeRing (X := Y) j
  have heX : IsOpenMap eX := schemeCoefficientOpen_proof C R K X j hj
  have heY : IsOpenEmbedding eY :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (schemeCoefficientContinuity_proof C R K Y j hj.continuous)
      (schemeSeparatedCoefficientInjectivity_proof C R K Y j hj.injective)
      (schemeCoefficientOpen_proof C R K Y j hj)
  apply heY.isOpenMap_iff.mpr
  have heq : eY ∘ (fun p : RingPoint C X R => p ≫ f) =
      (fun p : RingPoint C X K => p ≫ f) ∘ eX := by
    funext p
    exact (Category.assoc _ _ _).symm
  rw [heq]
  exact (isOpenMap_completeFieldCoefficientSmoothPointMap C K f).comp heX

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open scoped Langlands.Global.FixedModelLocalProduct

set_option backward.isDefEq.respectTransparency false

/-- Smooth openness at native curve-place factors, with their original topology
and the scalar action restricted from the enlarged level. -/
theorem curvePlaceSmoothLocalPointOpen : CurvePlaceSmoothLocalPointOpenStatement.{u} := by
  intro k F _ _ _ S X Y _ _ _ _ f _ T i
  cases i with
  | inl v =>
    let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v.1) :=
      inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F T.val (.inl v)))
    let : (Valued.v : Valuation (curvePlaceCompletion v.1)
        (WithZero (Multiplicative ℤ))).RankOne :=
      Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
    let : NontriviallyNormedField (curvePlaceCompletion v.1) :=
      Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
    exact isOpenMap_completeFieldCoefficientSmoothPointMap
      (curvePlaceSIntegers k F S) (curvePlaceCompletion v.1) f
  | inr v =>
    let : IsTopologicalRing (curvePlaceCompletionIntegers v.1) :=
      Subring.instIsTopologicalRing (curvePlaceCompletionIntegers v.1).toSubring
    let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1) :=
      inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F T.val (.inr v)))
    let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v.1) :=
      ((curvePlaceCompletionIntegers v.1).subtype.comp
        (algebraMap (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1))).toAlgebra
    let j : curvePlaceCompletionIntegers v.1 →ₐ[curvePlaceSIntegers k F S]
        curvePlaceCompletion v.1 :=
      { (curvePlaceCompletionIntegers v.1).subtype with commutes' := fun _ => rfl }
    let : (Valued.v : Valuation (curvePlaceCompletion v.1)
        (WithZero (Multiplicative ℤ))).RankOne :=
      Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
    let : NontriviallyNormedField (curvePlaceCompletion v.1) :=
      Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
    exact isOpenMap_integralCoefficientSmoothPointMap
      (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1)
      (curvePlaceCompletion v.1) f j
      (Valued.isOpen_valuationSubring (curvePlaceCompletion v.1)).isOpenEmbedding_subtypeVal

set_option maxHeartbeats 800000 in
/-- Smooth openness at every native number-field factor, including all infinite
places, with the original scalar action and topology. -/
theorem numberFieldSmoothLocalPointOpen : NumberFieldSmoothLocalPointOpenStatement.{u} := by
  intro K _ _ S X Y _ _ _ _ f _ T i
  cases i with
  | inl v =>
    let : Algebra ((S : Set (FinitePlace K)).integer K) (InfiniteCompletion K v) :=
      inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K T.val (.inl v)))
    let : NontriviallyNormedField (InfiniteCompletion K v) :=
      { (inferInstance : NormedField (InfiniteCompletion K v)) with
        non_trivial := by
          refine ⟨2, ?_⟩
          have h :=
            (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
              (map_zero (NumberField.InfinitePlace.Completion.extensionEmbedding v))
              (2 : InfiniteCompletion K v)
          rw [← h]
          norm_num only [map_ofNat, Complex.norm_ofNat] }
    exact isOpenMap_completeFieldCoefficientSmoothPointMap
      ((S : Set (FinitePlace K)).integer K) (InfiniteCompletion K v) f
  | inr i =>
    cases i with
    | inl v =>
      let : Algebra ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
        inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K T.val (.inr (.inl v))))
      let : (Valued.v : Valuation (FiniteCompletion K v.1)
          (WithZero (Multiplicative ℤ))).RankOne :=
        Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
      let : NontriviallyNormedField (FiniteCompletion K v.1) :=
        Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
      exact isOpenMap_completeFieldCoefficientSmoothPointMap
        ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) f
    | inr v =>
      let : IsTopologicalRing (v.1.adicCompletionIntegers K) :=
        Subring.instIsTopologicalRing (v.1.adicCompletionIntegers K).toSubring
      let : Algebra ((S : Set (FinitePlace K)).integer K) (v.1.adicCompletionIntegers K) :=
        inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K T.val (.inr (.inr v))))
      let : Algebra ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
        ((v.1.adicCompletionIntegers K).subtype.comp
          (algebraMap ((S : Set (FinitePlace K)).integer K)
            (v.1.adicCompletionIntegers K))).toAlgebra
      let j : v.1.adicCompletionIntegers K →ₐ[((S : Set (FinitePlace K)).integer K)]
          FiniteCompletion K v.1 :=
        { (v.1.adicCompletionIntegers K).subtype with commutes' := fun _ => rfl }
      let : (Valued.v : Valuation (FiniteCompletion K v.1)
          (WithZero (Multiplicative ℤ))).RankOne :=
        Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
      let : NontriviallyNormedField (FiniteCompletion K v.1) :=
        Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
      exact isOpenMap_integralCoefficientSmoothPointMap
        ((S : Set (FinitePlace K)).integer K) (v.1.adicCompletionIntegers K)
        (FiniteCompletion K v.1) f j
        (Valued.isOpen_valuationSubring (FiniteCompletion K v.1)).isOpenEmbedding_subtypeVal

/-- The exact local-openness input to the actual fixed-model adelic reduction. -/
theorem adelicSmoothLocalPointOpen : AdelicSmoothLocalPointOpenStatement.{u} :=
  ⟨curvePlaceSmoothLocalPointOpen, numberFieldSmoothLocalPointOpen⟩

end Langlands.Global
