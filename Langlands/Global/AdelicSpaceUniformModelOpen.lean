import Langlands.AlgebraicGeometry.AlgebraicSpace.OriginalBaseUniformLangWeilLifts
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompleteFieldSmoothPointOpenProof
import Langlands.Global.AdelicSpaceResidueComponentSurjectivity
import Langlands.Global.AdelicSpaceSmoothLocalOpenReduction

/-! # Actual model-level openness from the exact uniform estimate -/

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open NumberField

noncomputable section

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  [Algebra (ULift.{u} ℤ) (curvePlaceSIntegers k F S)]
  [LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ) (curvePlaceSIntegers k F S))]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- The exact space estimate gives cofinite surjectivity on all actual curve-place factors. -/
theorem curvePlaceSpaceFactor_eventually_surjective_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hYqs : IsQuasiSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := CurvePlaceLevelFactor k F S i) f) := by
  obtain ⟨c, hc, hb⟩ := OriginalBaseUniformLangWeilLifts.exists_bound
    (curvePlaceSIntegers k F S) hLW Y X f d hYqs hYft chart hchart hdim hsep hqc hsurj hconn
  let : SmoothOfRelativeDimension d chart.schemeMap.left := hdim
  have hf : IsSmoothMorphism f :=
    ⟨chart.source, chart.target, chart.sourceMap, chart.targetMap, chart.schemeMap,
      chart.sourceEtale, hchart, chart.targetEtale,
      SmoothOfRelativeDimension.smooth d chart.schemeMap.left, chart.comm⟩
  apply curvePlaceSpaceFactor_eventually_surjective_of_residue_bound k F S f hf d hc.le
  intro v x
  let : Module.Finite k v.1.ResidueField := functionFieldPlaceResidue k F v.1
  let : Finite v.1.ResidueField := Module.finite_of_finite k
  let : Finite (IsLocalRing.ResidueField (CurvePlaceLevelFactor k F S (.inr v))) :=
    Finite.of_equiv v.1.ResidueField (curvePlaceCompletionResidueEquiv v.1).toEquiv
  exact hb _ x

/-- Actual original-base point lifts outside one finite exceptional curve-place factor set. -/
def curvePlaceSpacePointLifts_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hYqs : IsQuasiSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ E : Finset (CurvePlaceLevelFactorIndex k F S),
      (i : CurvePlaceLevelFactorIndex k F S) → i ∉ E →
        (p : RingPoints (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F S i)) →
          {q : RingPoints (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F S i) //
            RingPoints.map f q = p} :=
  cofiniteSpacePointLifts (fun i => CurvePlaceLevelFactor k F S i) f
    (curvePlaceSpaceFactor_eventually_surjective_of_uniformLangWeil k F S hLW hYqs hYft
      f d chart hchart hdim hsep hqc hsurj hconn)

/-- With the fixed-dimensional model hypotheses, the exact estimate gives an actual open level map. -/
theorem curvePlaceSpaceLevel_isOpenMap_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (curvePlaceSpaceLevelTopology k F S X)
      (curvePlaceSpaceLevelTopology k F S Y) (RingPoints.map f) := by
  let : SmoothOfRelativeDimension d chart.schemeMap.left := hdim
  have hf : IsSmoothMorphism f :=
    ⟨chart.source, chart.target, chart.sourceMap, chart.targetMap, chart.schemeMap,
      chart.sourceEtale, hchart, chart.targetEtale,
      SmoothOfRelativeDimension.smooth d chart.schemeMap.left, chart.comm⟩
  exact curvePlaceSpaceLevel_isOpenMap_of_smooth k F S completeFieldSmoothSpacePointOpen
    hS hX hXft hY hYft f hf
    (curvePlaceSpaceFactor_eventually_surjective_of_uniformLangWeil k F S hLW
      (HenselianFinitePointProperProof.isQuasiSeparated_of_isSeparated hY) hYft
      f d chart hchart hdim hsep hqc hsurj hconn)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  [Algebra (ULift.{u} ℤ) ((S : Set (FinitePlace K)).integer K)]
  [LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ) ((S : Set (FinitePlace K)).integer K))]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- The exact estimate gives cofinite surjectivity on the full number-field factor index. -/
theorem numberFieldSpaceFactor_eventually_surjective_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hYqs : IsQuasiSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := NumberFieldLevelFactor K S i) f) := by
  obtain ⟨c, hc, hb⟩ := OriginalBaseUniformLangWeilLifts.exists_bound
    ((S : Set (FinitePlace K)).integer K) hLW Y X f d hYqs hYft chart hchart hdim
    hsep hqc hsurj hconn
  let : SmoothOfRelativeDimension d chart.schemeMap.left := hdim
  have hf : IsSmoothMorphism f :=
    ⟨chart.source, chart.target, chart.sourceMap, chart.targetMap, chart.schemeMap,
      chart.sourceEtale, hchart, chart.targetEtale,
      SmoothOfRelativeDimension.smooth d chart.schemeMap.left, chart.comm⟩
  apply numberFieldSpaceFactor_eventually_surjective_of_residue_bound K S f hf d hc.le
  intro v x
  let : Finite (IsLocalRing.ResidueField (NumberFieldLevelFactor K S (.inr (.inr v)))) :=
    CompletionResidue.finite_adicResidueField K v.1
  exact hb _ x

/-- Actual point lifts outside one finite exceptional set in the full number-field index. -/
def numberFieldSpacePointLifts_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hYqs : IsQuasiSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ E : Finset (NumberFieldLevelFactorIndex K S),
      (i : NumberFieldLevelFactorIndex K S) → i ∉ E →
        (p : RingPoints ((S : Set (FinitePlace K)).integer K) Y (NumberFieldLevelFactor K S i)) →
          {q : RingPoints ((S : Set (FinitePlace K)).integer K) X (NumberFieldLevelFactor K S i) //
            RingPoints.map f q = p} :=
  cofiniteSpacePointLifts (fun i => NumberFieldLevelFactor K S i) f
    (numberFieldSpaceFactor_eventually_surjective_of_uniformLangWeil K S hLW hYqs hYft
      f d chart hchart hdim hsep hqc hsurj hconn)

/-- The complete-field theorem and exact uniform estimate give an actual open number-field level map. -/
theorem numberFieldSpaceLevel_isOpenMap_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (numberFieldSpaceLevelTopology K S X)
      (numberFieldSpaceLevelTopology K S Y) (RingPoints.map f) := by
  let : SmoothOfRelativeDimension d chart.schemeMap.left := hdim
  have hf : IsSmoothMorphism f :=
    ⟨chart.source, chart.target, chart.sourceMap, chart.targetMap, chart.schemeMap,
      chart.sourceEtale, hchart, chart.targetEtale,
      SmoothOfRelativeDimension.smooth d chart.schemeMap.left, chart.comm⟩
  exact numberFieldSpaceLevel_isOpenMap_of_smooth K S completeFieldSmoothSpacePointOpen
    hX hXft hY hYft f hf
    (numberFieldSpaceFactor_eventually_surjective_of_uniformLangWeil K S hLW
      (HenselianFinitePointProperProof.isQuasiSeparated_of_isSeparated hY) hYft
      f d chart hchart hdim hsep hqc hsurj hconn)

end NumberField

end Langlands.Global
