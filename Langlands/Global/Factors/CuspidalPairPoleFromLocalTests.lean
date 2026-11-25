import Langlands.Global.Factors.CuspidalPairPoleEqualTestGrowth
import Langlands.Global.Factors.CuspidalPairPoleUnequalTestGrowth
import Langlands.Global.Factors.CuspidalPairPoleLocalRanges
import Langlands.Global.Factors.CuspidalPairPoleTCReduction

/-! # The pole theorem from the ordinary local tests and completed functional equation -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal ArchimedeanLocal CompletionPadic
open LocalFactor.Archimedean CuspidalPairFunctionalEquation
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

/-- The normalized strip growth needed for ordinary real local tests with the
compatible quotient measures chosen in the global construction. -/
def RealOrdinaryNormalizedStripGrowthStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List RealBlock), realRank d = r + 1 → realRank e = t + 1 →
    ∀ a : ℝˣ, HasOrdinaryNormalizationStripGrowth
      (realOrdinaryUnequalTest h d e a (realQuotientMeasureData t)) (realPairLFactor d e)) ∧
  ∀ (r : ℕ) (d e : List RealBlock), realRank d = r + 1 → realRank e = r + 1 →
    ∀ a : ℝˣ, HasOrdinaryNormalizationStripGrowth
      (realOrdinaryEqualTest r d e a (realQuotientMeasureData r)) (realPairLFactor d e)

/-- The normalized strip growth needed for ordinary complex local tests with the
compatible quotient measures chosen in the global construction. -/
def ComplexOrdinaryNormalizedStripGrowthStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = t + 1 →
    ∀ a : ℂˣ, HasOrdinaryNormalizationStripGrowth
      (complexOrdinaryUnequalTest h d e a (complexQuotientMeasureData t)) (complexPairLFactor d e)) ∧
  ∀ (r : ℕ) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
    ∀ a : ℂˣ, HasOrdinaryNormalizationStripGrowth
      (complexOrdinaryEqualTest r d e a (complexQuotientMeasureData r)) (complexPairLFactor d e)

/-- The local inputs to the ordinary test construction over every number field. -/
def CuspidalPairOrdinaryLocalInputs : Prop :=
  ArchimedeanOrdinaryNormalizedTestsStatement ∧
  RealOrdinaryNormalizedStripGrowthStatement ∧ ComplexOrdinaryNormalizedStripGrowthStatement ∧
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    SpecifiedWhittakerSliceComparisonAt.{u,uQ} F

/-- Local test inputs over one number field. The real analytic clauses are
used only when the field has a real place. -/
def CuspidalPairOrdinaryLocalInputsAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  (Nonempty {v : InfinitePlace F // v.IsReal} →
    RealOrdinaryNormalizedContinuationStatement ∧ RealOrdinaryNormalizedGenerationStatement ∧
    RealOrdinaryNormalizedStripGrowthStatement) ∧
  ComplexOrdinaryNormalizedContinuationStatement ∧ ComplexOrdinaryNormalizedGenerationStatement ∧
  ComplexOrdinaryNormalizedStripGrowthStatement ∧ SpecifiedWhittakerSliceComparisonAt.{u,uQ} F

private theorem equalCoveringNormalizedProduct_of_local_at
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hLocal : CuspidalPairOrdinaryLocalInputsAt.{u,uQ} F)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (r : ℕ) :
    EqualCoveringNormalizedProductAt.{u,uQ} F r ψ
      (fun R => (∃ z, R z ≠ 0) ∧ HasStripExponentialGrowth R) := by
  obtain ⟨hReal, hNC, hGC, hGrowC, hSlice⟩ := hLocal
  intro T T' hT hT' P P' hP hP' c dR dR' hdR hdR' dC dC' hdC hdC'
  choose aR haR using fun v => exists_isRealAdditiveComponent ψ hψ v
  choose aC haC using fun w => exists_isComplexAdditiveComponent ψ hψ w
  have hM := hSlice ψ hψ r T hT P hP aR haR aC haC dR hdR dC hdC
  have hM' := hSlice ψ hψ r T' hT' P' hP' aR haR aC haC dR' hdR' dC' hdC'
  let M := hM.choose
  let M' := hM'.choose_spec.choose
  have hR := hM.choose_spec.choose_spec.1
  have hR' := hM'.choose_spec.choose_spec.2
  have hGrowR (v : {v : InfinitePlace F // v.IsReal}) :=
    (hReal ⟨v⟩).2.2.2 r (dR v) (dR' v) (hdR v).1 (hdR' v).1 (aR v)
  have hGrowthC (w : {w : InfinitePlace F // w.IsComplex}) :=
    hGrowC.2 r (dC w) (dC' w) (hdC w).1 (hdC' w).1 (aC w)
  refine exists_equalNormalizedFamily_of_local_at c hT hT' hψ (fun v => (hReal v).1) hNC
    (fun v => (hReal v).2.1) hGC M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' ?_
  intro S hPS hPS' hS
  let ψv (v : S) := canonicalFiniteAdditiveComponent ψ hψ v.1
  have hψv (v : S) : IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v) :=
    isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hψ v.1
  let ν (v : S) : LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v) :=
    ⟨Correspondence.localSelfDualHaar (padicField v.1) (ψv v),
      Correspondence.isSelfDual_localSelfDualHaar (padicField v.1) (ψv v)⟩
  have hg := exists_growthNormalizedEqualTest_of_local_at c hPS hPS' hT hT' hψ hS hψv ν
    (fun v => (hReal v).2.1) hGC M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' hGrowR hGrowthC 0
  exact ⟨hg.choose, ⟨0, hg.choose_spec.1⟩, hg.choose_spec.2⟩

private theorem unequalNormalizedProduct_of_local_at
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hLocal : CuspidalPairOrdinaryLocalInputsAt.{u,uQ} F) : UnequalNormalizedProductAt.{u,uQ} F := by
  obtain ⟨hReal, _, hGC, hGrowC, hSlice⟩ := hLocal
  intro ψ hψ r t hrt T T' hT hT' P P' hP hP' c dR dR' hdR hdR' dC dC' hdC hdC'
  choose aR haR using fun v => exists_isRealAdditiveComponent ψ hψ v
  choose aC haC using fun w => exists_isComplexAdditiveComponent ψ hψ w
  have hM := hSlice ψ hψ r T hT P hP aR haR aC haC dR hdR dC hdC
  have hM' := hSlice ψ hψ t T' hT' P' hP' aR haR aC haC dR' hdR' dC' hdC'
  let M := hM.choose
  let M' := hM'.choose_spec.choose
  have hR := hM.choose_spec.choose_spec.1
  have hR' := hM'.choose_spec.choose_spec.2
  obtain ⟨A, hA⟩ := exists_finiteAdditiveSupport ψ hψ
  let S := (P.exceptional ∪ P'.exceptional) ∪ A
  have hPS : P.exceptional ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hPS' : P'.exceptional ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hS := finiteAdditiveSupport_mono hA (S' := S) Finset.subset_union_right
  let ψv (v : S) := canonicalFiniteAdditiveComponent ψ hψ v.1
  have hψv (v : S) : IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v) :=
    isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hψ v.1
  let ν (v : S) : LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v) :=
    ⟨Correspondence.localSelfDualHaar (padicField v.1) (ψv v),
      Correspondence.isSelfDual_localSelfDualHaar (padicField v.1) (ψv v)⟩
  refine ⟨S, hPS, hPS', hS, hasCoveringUnequalNormalizedGrowthTests_of_local_at c hrt hPS hPS' hT hT'
    hψ hS hψv ν (fun v => (hReal v).2.1) hGC M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' ?_ ?_⟩
  · intro v
    exact (hReal ⟨v⟩).2.2.1 r t hrt (dR v) (dR' v) (hdR v).1 (hdR' v).1 (aR v)
  · intro w
    exact hGrowC.1 r t hrt (dC w) (dC' w) (hdC w).1 (hdC' w).1 (aC w)

private theorem equalPairCompletion_of_local_at
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hLocal : CuspidalPairOrdinaryLocalInputsAt.{u,uQ} F) : EqualPairCompletionAt.{u,uQ} F := by
  intro ψ hψ r T T' hT hT' P P' h h' c dR dR' hdR hdR' dC dC' hdC hdC'
  simpa only [HasNormalizedStripTest, and_assoc] using
    equalPairCompletion_of_covering_normalized_products_at F r ψ hψ
      (equalCoveringNormalizedProduct_of_local_at hLocal ψ hψ r) T T' hT hT' P P' h h' c
      dR dR' hdR hdR' dC dC' hdC hdC'

/-- The actual ordinary local inputs and the completed functional equation imply the
published cuspidal pair pole proposition in both universes. -/
def CuspidalPairPoleFromLocalTestsStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u,uQ} → CuspidalPairOrdinaryLocalInputs.{u,uQ} →
    CuspidalPairPoleStatement.{u,uQ}

/-- Construct both families of normalized tests and apply the global pole reduction. -/
theorem cuspidalPairPoleFromLocalTests : CuspidalPairPoleFromLocalTestsStatement.{u,uQ} := by
  intro hFE hLocal
  have hAt (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] :
      CuspidalPairOrdinaryLocalInputsAt.{u,uQ} F :=
    ⟨fun _ => ⟨hLocal.1.1, hLocal.1.2.2.1, hLocal.2.1⟩,
      hLocal.1.2.1, hLocal.1.2.2.2, hLocal.2.2.1, hLocal.2.2.2 F⟩
  exact cuspidalPairPole_of_equalCompletion hFE
    (fun F _ _ _ => equalPairCompletion_of_local_at (hAt F))
    (fun F _ _ _ => unequalNormalizedProduct_of_local_at (hAt F))

/-- The complex ordinary test inputs give the required normalized continuation
at a totally complex field. -/
theorem cuspidalPairNormalizedContinuationTCAt_of_local
    (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)]
    (hNC : ComplexOrdinaryNormalizedContinuationStatement)
    (hGC : ComplexOrdinaryNormalizedGenerationStatement)
    (hGrowth : ComplexOrdinaryNormalizedStripGrowthStatement)
    (hSlice : SpecifiedWhittakerSliceComparisonAt.{u,uQ} F) :
    CuspidalPairNormalizedContinuationTCAt.{u,uQ} F := by
  intro ψ hψ r t T T' hT hT' P P' h h' c dC dC' hdC hdC'
  let : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex v.1) v.2⟩
  have hLocal : CuspidalPairOrdinaryLocalInputsAt.{u,uQ} F :=
    ⟨fun ⟨v⟩ => isEmptyElim v, hNC, hGC, hGrowth, hSlice⟩
  let dR : {v : InfinitePlace F // v.IsReal} → List RealBlock := isEmptyElim
  have hcont := exists_completion_of_normalized_products_at
    (equalPairCompletion_of_local_at hLocal) (unequalNormalizedProduct_of_local_at hLocal)
    ψ hψ hT hT' c dR dR isEmptyElim isEmptyElim dC dC' hdC hdC'
  simpa only [archimedeanPairProduct_eq_complex_of_totallyComplex, HasNormalizedStripTest] using hcont

/-- Complex local continuation, generation, strip growth and actual slice
ranges yield the totally complex pole theorem with the completed equation. -/
def CuspidalPairPoleTCFromLocalTestsStatement : Prop :=
  CuspidalPairCompletedEquationTCStatement.{u,uQ} →
  ComplexOrdinaryNormalizedContinuationStatement → ComplexOrdinaryNormalizedGenerationStatement →
  ComplexOrdinaryNormalizedStripGrowthStatement →
  (∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)], SpecifiedWhittakerSliceComparisonAt.{u,uQ} F) →
  CuspidalPairPoleTCStatement.{u,uQ}

theorem cuspidalPairPoleTCFromLocalTests : CuspidalPairPoleTCFromLocalTestsStatement.{u,uQ} := by
  intro hFE hNC hGC hGrowth hSlice
  exact cuspidalPairPoleTCReduction hFE fun F _ _ _ _ =>
    cuspidalPairNormalizedContinuationTCAt_of_local F hNC hGC hGrowth (hSlice F)

end Langlands.Global.CuspidalPairPoles
