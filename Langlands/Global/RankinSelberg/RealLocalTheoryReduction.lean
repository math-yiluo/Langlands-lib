import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Global.RankinSelberg.RealPlacePositiveAnalyticReduction

/-! # Local analytic and model inputs for the real-place functional equation -/

noncomputable section
universe u

open NumberField MeasureTheory
open Langlands.LocalFactor.Archimedean Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := borel _
local instance (r : ℕ) : BorelSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

/-- Unequal-rank analytic equations on the specified local coefficient space.
All analytic and continuous-model normalization work remains in this premise. -/
def RealLocalUnequalJacquetStatement : Prop := by
  classical
  exact
  ∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = t + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    W ∈ realWhittakerModel r ds a → W' ∈ realWhittakerModel t es (-a) →
    RealJacquet.UnequalEquation h a D W W' ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) (-a)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) *
        (RealJacquet.determinant es (-1) : ℂ))

/-- Positive equal-rank analytic equations on the local coefficient space. -/
def RealLocalPositiveEqualJacquetStatement : Prop := by
  classical
  exact
  ∀ (r : ℕ), 0 < r → ∀ (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = r + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    W ∈ realWhittakerModel r ds a → W' ∈ realWhittakerModel r es (-a) →
    RealJacquet.EqualEquation a (-a) D W W' Φ ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ r)

/-- Actual global restrictions belong to the specified local coefficient space.
This is a retained model-membership theorem, not a consequence of the definition. -/
def RealPlaceWhittakerModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ ds : List RealBlock, T.realization.HasRealPlaceParameter v ds →
  ∀ W : Langlands.GeneralLinear (r + 1) ℝ → ℂ,
    (IsRealPlaceWhittaker F T ψ.complex v W → W ∈ realWhittakerModel r ds a) ∧
    (IsRealPlaceWhittaker F T ψ.complex⁻¹ v W → W ∈ realWhittakerModel r ds (-a))

/-- The dual pair factor of actual contragredient parameters is the factor of
the explicitly dualized blocks. Only denominator equality is required. -/
def RealPlaceContragredientPairLStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T Td : Automorphic.CuspidalOperatorRealization F r)
    (T' Td' : Automorphic.CuspidalOperatorRealization F t),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : {v : InfinitePlace F // v.IsReal}) (ds es dds ees : List RealBlock),
    T.realization.HasRealPlaceParameter v ds →
    T'.realization.HasRealPlaceParameter v es →
    Td.realization.HasRealPlaceParameter v dds →
    Td'.realization.HasRealPlaceParameter v ees →
    (realPairLFactor dds ees).denominator =
      (realPairLFactor (ds.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock)).denominator

namespace RealLocalJacquet

theorem realMinusOneScalar_eq_parameter
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsReal}) (ds : List RealBlock)
    (hds : T.realization.HasRealPlaceParameter v ds) :
    realMinusOneScalar T v = (RealJacquet.determinant ds (-1) : ℂ) := by
  have hn : ∃ f : Automorphic.realStandardKFinite (r + 1) ds, f ≠ 0 := by
    rw [← hds.1]
    exact realStandardKFiniteNonzero ds
  obtain ⟨f, hf⟩ := hn
  exact realMinusOneScalar_eq_parameter_of_nonzero T v ds hds f hf

end RealLocalJacquet

/-- Four explicitly open local analytic/model inputs imply the exact real-place target. -/
def RealPlaceLocalTheoryReductionStatement : Prop :=
  RealLocalUnequalJacquetStatement →
  RealLocalPositiveEqualJacquetStatement →
  RealPlaceWhittakerModelStatement.{u} →
  RealPlaceContragredientPairLStatement.{u} →
  RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceLocalTheoryReduction : RealPlaceLocalTheoryReductionStatement.{u} := by
  intro hU hE hB hD
  apply realPlacePositiveAnalyticReduction
  constructor
  · intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' v a ha
      ds es dds ees hds hes hdds hees D W W' hW hW'
    have hWm := (hB F ψ hψ r T v a ha ds hds W).1 hW
    have hWm' := (hB F ψ hψ t T' v a ha es hes W').2 hW'
    have hEq := hU r t h ds es hds.1 hes.1 a D W W' hWm hWm'
    have hDen := hD F r t T Td T' Td' hTd hTd' v ds es dds ees hds hes hdds hees
    have hc := RealLocalJacquet.realMinusOneScalar_eq_parameter T v ds hds
    have hc' := RealLocalJacquet.realMinusOneScalar_eq_parameter T' v es hes
    simpa only [RealJacquet.UnequalEquation, ← hDen, ← hc, ← hc'] using hEq
  · intro F _ _ _ ψ hψ r hr T Td T' Td' hTd hTd' v a ha
      ds es dds ees hds hes hdds hees D W W' Φ hW hW'
    have hWm := (hB F ψ hψ r T v a ha ds hds W).1 hW
    have hWm' := (hB F ψ hψ r T' v a ha es hes W').2 hW'
    have hEq := hE r hr ds es hds.1 hes.1 a D W W' Φ hWm hWm'
    have hDen := hD F r r T Td T' Td' hTd hTd' v ds es dds ees hds hes hdds hees
    have hc := RealLocalJacquet.realMinusOneScalar_eq_parameter T v ds hds
    simpa only [RealJacquet.EqualEquation, ← hDen, ← hc] using hEq

end Langlands.Global.RankinSelbergGlobal
