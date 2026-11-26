import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryTestsFromGeneration
import Langlands.Global.Factors.CuspidalPairPoleLocalRanges

/-! # Ordinary archimedean tests on the split centre and the untwisting premise

The ordinary nonvanishing statements of `ArchimedeanFactorizationOrdinaryReduction`, restricted
to cuspidal realizations trivial on the split centre (`CuspidalPairPoles.IsTrivialOnSplitCentre`),
follow from local normalized generation and the published restriction surjectivity statements
of `CuspidalPairPoleLocalRanges`, which carry that hypothesis. The passage from these
restricted statements to arbitrary realizations is stated as the premise
`OrdinaryPlaceTestsUntwistStatement`. Hence `ArchimedeanFactorizationStatement` follows from
the slice comparison, the real-place functional equation, the two generation statements, the two
published surjectivity statements and that premise. See the paired Markdown.
-/

noncomputable section
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal
open Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.CuspidalPairPoles (IsTrivialOnSplitCentre)

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- `RealUnequalOrdinaryPlaceTestsStatement` for realizations trivial on the split centre. -/
def RealUnequalOrdinaryPlaceTestsSplitCentreStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (v : RP F) (a : ℝˣ), IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' : List RealBlock),
    T.realization.HasRealPlaceParameter v d → T'.realization.HasRealPlaceParameter v d' →
    ∃ (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (D : RealQuotientMeasureData t),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realUnequalIntegral h D W W' s ≠ 0

/-- `ComplexUnequalOrdinaryPlaceTestsStatement` for realizations trivial on the split centre. -/
def ComplexUnequalOrdinaryPlaceTestsSplitCentreStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (w : CP F) (a : ℂˣ), IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d → T'.realization.HasComplexPlaceParameter w d' →
    ∃ (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
      (D : ComplexQuotientMeasureData t),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ complexUnequalIntegral h D W W' s ≠ 0

/-- `RealEqualOrdinaryPlaceTestsPositiveRankStatement` for realizations trivial on the split
centre. -/
def RealEqualOrdinaryPlaceTestsSplitCentreStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ), 0 < r →
  ∀ (T T' : CuspidalOperatorRealization F r),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (v : RP F) (a : ℝˣ), IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' : List RealBlock),
    T.realization.HasRealPlaceParameter v d → T'.realization.HasRealPlaceParameter v d' →
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ) (D : RealQuotientMeasureData r),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realEqualIntegral D W W' Φ s ≠ 0

/-- `ComplexEqualOrdinaryPlaceTestsPositiveRankStatement` for realizations trivial on the split
centre. -/
def ComplexEqualOrdinaryPlaceTestsSplitCentreStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ), 0 < r →
  ∀ (T T' : CuspidalOperatorRealization F r),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (w : CP F) (a : ℂˣ), IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d → T'.realization.HasComplexPlaceParameter w d' →
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) (D : ComplexQuotientMeasureData r),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ complexEqualIntegral D W W' Φ s ≠ 0

/-- **Untwisting premise.** Each ordinary nonvanishing statement for realizations trivial on
the split centre implies the same statement for all actual cuspidal realizations. -/
def OrdinaryPlaceTestsUntwistStatement : Prop :=
  (RealUnequalOrdinaryPlaceTestsSplitCentreStatement.{u} →
      RealUnequalOrdinaryPlaceTestsStatement.{u}) ∧
    (ComplexUnequalOrdinaryPlaceTestsSplitCentreStatement.{u} →
      ComplexUnequalOrdinaryPlaceTestsStatement.{u}) ∧
    (RealEqualOrdinaryPlaceTestsSplitCentreStatement.{u} →
      RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u}) ∧
    (ComplexEqualOrdinaryPlaceTestsSplitCentreStatement.{u} →
      ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u})

/-- Real generation and the published real surjectivity give both real ordinary statements on
the split centre. -/
theorem realOrdinaryPlaceTestsSplitCentre_of_generation
    (hG : RealOrdinaryNormalizedGenerationStatement)
    (hS : CuspidalPairPoles.RealPlaceWhittakerRestrictionSurjectivityStatement.{u}) :
    RealUnequalOrdinaryPlaceTestsSplitCentreStatement.{u} ∧
      RealEqualOrdinaryPlaceTestsSplitCentreStatement.{u} :=
  ⟨fun F _ _ _ ψ hψ r t h T T' hT hT' v a ha _ _ hd hd' =>
    exists_realUnequalOrdinaryTest ψ hψ hG h T T' v a ha hd hd'
      (fun W => (hS F ψ hψ r T hT v a ha _ hd W).1) (fun W => (hS F ψ hψ t T' hT' v a ha _ hd' W).2),
    fun F _ _ _ ψ hψ r _ T T' hT hT' v a ha _ _ hd hd' =>
    exists_realEqualOrdinaryTest ψ hψ hG T T' v a ha hd hd'
      (fun W => (hS F ψ hψ r T hT v a ha _ hd W).1) (fun W => (hS F ψ hψ r T' hT' v a ha _ hd' W).2)⟩

/-- Complex generation and the published complex surjectivity give both complex ordinary
statements on the split centre. -/
theorem complexOrdinaryPlaceTestsSplitCentre_of_generation
    (hG : ComplexOrdinaryNormalizedGenerationStatement)
    (hS : CuspidalPairPoles.ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u}) :
    ComplexUnequalOrdinaryPlaceTestsSplitCentreStatement.{u} ∧
      ComplexEqualOrdinaryPlaceTestsSplitCentreStatement.{u} :=
  ⟨fun F _ _ _ ψ hψ r t h T T' hT hT' w a ha _ _ hd hd' =>
    exists_complexUnequalOrdinaryTest ψ hψ hG h T T' w a ha hd hd'
      (fun W => (hS F ψ hψ r T hT w a ha _ hd W).1) (fun W => (hS F ψ hψ t T' hT' w a ha _ hd' W).2),
    fun F _ _ _ ψ hψ r _ T T' hT hT' w a ha _ _ hd hd' =>
    exists_complexEqualOrdinaryTest ψ hψ hG T T' w a ha hd hd'
      (fun W => (hS F ψ hψ r T hT w a ha _ hd W).1) (fun W => (hS F ψ hψ r T' hT' w a ha _ hd' W).2)⟩

/-- **Conditional factorization through the split centre.** -/
def ArchimedeanFactorizationSplitCentreReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} → RealPlaceFunctionalEquationStatement.{u} →
    RealOrdinaryNormalizedGenerationStatement → ComplexOrdinaryNormalizedGenerationStatement →
    CuspidalPairPoles.RealPlaceWhittakerRestrictionSurjectivityStatement.{u} →
    CuspidalPairPoles.ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} →
    OrdinaryPlaceTestsUntwistStatement.{u} → ArchimedeanFactorizationStatement.{u, uQ}

/-- Proof: the split-centre ordinary statements, untwisted by the premise, feed
`archimedeanFactorizationOrdinaryReduction`. -/
theorem archimedeanFactorizationSplitCentreReduction :
    ArchimedeanFactorizationSplitCentreReductionStatement.{u, uQ} :=
  fun hSlice hRealFE hGR hGC hSR hSC hU =>
    archimedeanFactorizationOrdinaryReduction hSlice hRealFE
      (hU.1 (realOrdinaryPlaceTestsSplitCentre_of_generation hGR hSR).1)
      (hU.2.1 (complexOrdinaryPlaceTestsSplitCentre_of_generation hGC hSC).1)
      (hU.2.2.1 (realOrdinaryPlaceTestsSplitCentre_of_generation hGR hSR).2)
      (hU.2.2.2 (complexOrdinaryPlaceTestsSplitCentre_of_generation hGC hSC).2)

end Langlands.Global.RankinSelbergGlobal
