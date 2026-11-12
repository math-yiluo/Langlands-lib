import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartSecondCountable
import Langlands.Global.AdelicSpacePointStagesProof
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.FunctionFieldAdelesSecondCountableProof

/-!
# Second countability of adelic levels of separated algebraic spaces

For a separated algebraic space of finite type over the `S`-integers of a global field, every
factor of a level is second countable. Over a completion this follows from
`EtaleChartSecondCountable`: the completions are second countable and have a countable Galois
family. Over a completed valuation ring the factor carries the topology induced from the
completion. The level is a countable product of factors, and a stage is homeomorphic to a
level.
-/

noncomputable section

universe u

open CategoryTheory Topology Polynomial
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)
open Langlands.FieldTheory.CountableGaloisFamily
open NumberField (RingOfIntegers)

namespace Langlands.Global

namespace AdelicSpaceLevelSecondCountable

open AdelicSpaceLocalFields

/-- A field-valued factor over a henselian valued field with a countable base and a countable
Galois family is second countable. -/
theorem secondCountableTopology_fieldValued {C : Type u} [CommRing C]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))} {A L : Type u} [CommRing A] [Algebra C A]
    [NontriviallyNormedField L] [Algebra C L] (hK : IsHenselianValuedField L)
    [SecondCountableTopology L] (hfam : HasCountableGaloisFamily L) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing C X) (φ : A →ₐ[C] L) :
    @SecondCountableTopology _ (fieldValuedPointTopology C X φ) := by
  have := EtaleChartSecondCountable.secondCountableTopology_etaleChartTopology hK hfam
    hX.baseChange (finiteTypeOverRing_baseChange (Spec.algebraMap C L) hft)
  let _ := etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  exact @TopologicalSpace.secondCountableTopology_induced _ _ _ this (fieldValuedPointMap C X φ)

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- The archimedean completions have a countable Galois family. -/
theorem infinite_hasCountableGaloisFamily (v : InfinitePlace K) :
    HasCountableGaloisFamily (InfiniteCompletion K v) := by
  have : CharZero (InfiniteCompletion K v) :=
    charZero_of_injective_algebraMap (algebraMap K (InfiniteCompletion K v)).injective
  refine hasCountableGaloisFamily_of_natDegree_le_two fun p hp => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have hirr : Irreducible (p.map (e : InfiniteCompletion K v →+* ℝ)) :=
      (MulEquiv.irreducible_iff (Polynomial.mapEquiv e).toMulEquiv).mpr hp
    rw [← natDegree_map_eq_of_injective e.injective p]
    exact hirr.natDegree_le_two
  · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    have hirr : Irreducible (p.map (e : InfiniteCompletion K v →+* ℂ)) :=
      (MulEquiv.irreducible_iff (Polynomial.mapEquiv e).toMulEquiv).mpr hp
    rw [← natDegree_map_eq_of_injective e.injective p]
    have := IsAlgClosed.degree_eq_one_of_irreducible ℂ hirr
    exact (natDegree_eq_of_degree_eq_some this).le.trans (by norm_num)

variable (T : Finset (FinitePlace K))
  {X : AlgebraicSpace (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K)))}

/-- Every factor of a number-field level is second countable. -/
theorem numberField_factor (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) X)
    (i : NumberFieldLevelFactorIndex K T) :
    @SecondCountableTopology _
      (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K T i)) := by
  rcases i with v | v | v
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inl v)) := infiniteNormedField K v
    have : SecondCountableTopology (InfiniteCompletion K v) :=
      infiniteCompletion_secondCountableTopology K v
    exact @secondCountableTopology_fieldValued _ _ X _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inl v)) (infinite_isHenselianValuedField K v) this
      (infinite_hasCountableGaloisFamily K v) hX hft _
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inl v))) :=
      normedField (RingOfIntegers K) K v.1
    have : SecondCountableTopology (FiniteCompletion K v.1) :=
      finiteCompletion_secondCountableTopology K v.1
    have hfam : HasCountableGaloisFamily (FiniteCompletion K v.1) :=
      @hasCountableGaloisFamily_of_isUltrametricDist _ N
        (isUltrametricDist (RingOfIntegers K) K v.1) (completeSpace (RingOfIntegers K) K v.1)
        (finiteCompletion_separableSpace K v.1)
    exact @secondCountableTopology_fieldValued _ _ X _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inl v)))
      (isHenselianValuedField (RingOfIntegers K) K v.1) this hfam hX hft _
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inr v))) :=
      normedField (RingOfIntegers K) K v.1
    have : SecondCountableTopology (FiniteCompletion K v.1) :=
      finiteCompletion_secondCountableTopology K v.1
    have hfam : HasCountableGaloisFamily (FiniteCompletion K v.1) :=
      @hasCountableGaloisFamily_of_isUltrametricDist _ N
        (isUltrametricDist (RingOfIntegers K) K v.1) (completeSpace (RingOfIntegers K) K v.1)
        (finiteCompletion_separableSpace K v.1)
    exact @secondCountableTopology_fieldValued _ _ X _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inr v)))
      (isHenselianValuedField (RingOfIntegers K) K v.1) this hfam hX hft _

/-- **Levels are second countable**, number fields. -/
theorem numberField_level (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) X) :
    @SecondCountableTopology _ (numberFieldSpaceLevelTopology K T X) := by
  have : Countable (FinitePlace K) := finitePlace_countable K
  have : Countable (NumberFieldLevelFactorIndex K T) := by
    unfold NumberFieldLevelFactorIndex
    infer_instance
  let _ (i : NumberFieldLevelFactorIndex K T) : TopologicalSpace (RingPoints _ X
      (NumberFieldLevelFactor K T i)) := fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K T i)
  have := numberField_factor K T hX hft
  exact TopologicalSpace.secondCountableTopology_induced _ _ _

variable (S : Finset (FinitePlace K))
  {Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- **Stages are second countable**, number fields. -/
theorem numberField_stage (hY : IsSeparated Y)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (T : AdelicLevelIndexAbove S) :
    @SecondCountableTopology _ (numberFieldSpaceStageTopology K S Y T) := by
  have := numberField_level K T.val (X := numberFieldSpaceLevelBaseChange K T.property Y)
    hY.baseChange (finiteTypeOverRing_baseChange _ hft)
  exact @TopologicalSpace.secondCountableTopology_induced _ _
    (numberFieldSpaceLevelTopology K T.val _) this _

end NumberField

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F]

variable (T : Finset (AlgebraicCurve.Place k F))
  {X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F T)))}

omit [IsScalarTower k (RatFunc k) F] in
/-- Every factor of a curve-place level is second countable. -/
theorem curve_factor (hX : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F T) X)
    (i : CurvePlaceLevelFactorIndex k F T) :
    @SecondCountableTopology _
      (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F T i)) := by
  rcases i with v | v
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inl v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have : SecondCountableTopology (curvePlaceCompletion v.1) :=
      curvePlaceCompletion_secondCountableTopology k F v.1
    have hfam : HasCountableGaloisFamily (curvePlaceCompletion v.1) :=
      @hasCountableGaloisFamily_of_isUltrametricDist _ N
        (isUltrametricDist v.1.toValuationSubring F v.1.heightOneSpectrum)
        (completeSpace v.1.toValuationSubring F v.1.heightOneSpectrum)
        (curvePlaceCompletion_separableSpace k F v.1)
    exact @secondCountableTopology_fieldValued _ _ X _ _ _ _ N
      (instAdelicSpaceLevelTopology3 k F T (.inl v))
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum) this hfam hX hft _
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inr v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have : SecondCountableTopology (curvePlaceCompletion v.1) :=
      curvePlaceCompletion_secondCountableTopology k F v.1
    have hfam : HasCountableGaloisFamily (curvePlaceCompletion v.1) :=
      @hasCountableGaloisFamily_of_isUltrametricDist _ N
        (isUltrametricDist v.1.toValuationSubring F v.1.heightOneSpectrum)
        (completeSpace v.1.toValuationSubring F v.1.heightOneSpectrum)
        (curvePlaceCompletion_separableSpace k F v.1)
    exact @secondCountableTopology_fieldValued _ _ X _ _ _ _ N
      (instAdelicSpaceLevelTopology3 k F T (.inr v))
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum) this hfam hX hft _

/-- **Levels are second countable**, global function fields. -/
theorem curve_level (hX : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F T) X) :
    @SecondCountableTopology _ (curvePlaceSpaceLevelTopology k F T X) := by
  have : Countable (AlgebraicCurve.Place k F) := curvePlace_countable k F
  have : Countable (CurvePlaceLevelFactorIndex k F T) := by
    unfold CurvePlaceLevelFactorIndex
    infer_instance
  let _ (i : CurvePlaceLevelFactorIndex k F T) : TopologicalSpace (RingPoints _ X
      (CurvePlaceLevelFactor k F T i)) := fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F T i)
  have := curve_factor k F T hX hft
  exact TopologicalSpace.secondCountableTopology_induced _ _ _

variable (S : Finset (AlgebraicCurve.Place k F))
  {Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- **Stages are second countable**, global function fields. -/
theorem curve_stage (hY : IsSeparated Y) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (T : AdelicLevelIndexAbove S) :
    @SecondCountableTopology _ (curvePlaceSpaceStageTopology k F S Y T) := by
  have := curve_level k F T.val (X := curvePlaceSpaceLevelBaseChange k F T.property Y)
    hY.baseChange (finiteTypeOverRing_baseChange _ hft)
  exact @TopologicalSpace.secondCountableTopology_induced _ _
    (curvePlaceSpaceLevelTopology k F T.val _) this _

end Curve

end AdelicSpaceLevelSecondCountable

end Langlands.Global
