import Langlands.Global.RankinSelberg.EqualWhittakerPositiveRankReduction
import Langlands.Global.RankinSelberg.InfiniteWhittakerSmoothSlice
import Langlands.Global.RankinSelberg.EqualPlaceCommonTests
import Langlands.Global.RankinSelberg.RealPlaceEqualPairConvergence
import Langlands.Global.RankinSelberg.ComplexEqualPairConvergence

/-! # Equal-rank factorization from identity comparison and separate local witnesses -/

noncomputable section

open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic InfinitePlaceFamily
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.Global.HeckeFunctionalEquation
open Langlands.LocalFactor.Archimedean ArchimedeanLocal InfiniteWhittakerSlice

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- Evaluations of the actual one-place tensor slices at the full adelic identity
are proportional to those of a nonzero reference pure tensor. -/
def InfiniteWhittakerIdentityProportionalityPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
  ∀ (r : ℕ), 0 < r →
  ∀ (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hI : HasIrreducibleAdmissibleComponents P)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ),
  ∀ (dR : (RP F) → List RealBlock),
    (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
  ∀ (dC : (CP F) → List ComplexCharacterData),
    (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
  ∀ (a₀ : FiniteTensor P) (b₀ : ∀ i : Index F, T.placeDensityModels.subspace i),
    tensorWhittaker P hI χ a₀ b₀ 1 ≠ 0 →
  ∀ (a : FiniteTensor P) (i : Index F) (b : ∀ j : Index F, T.placeDensityModels.subspace j),
  ∃ c : ℂ, ∀ v : T.placeDensityModels.subspace i,
    sliceMap P hI χ hχ a i b 1 v 1 = c * sliceMap P hI χ hχ a₀ i b₀ 1 v 1

/-- The real ordinary and dual witnesses may use different test triples for one
quotient measure. Each witness has nonzero integral arbitrarily far to the right. -/
def RealEqualPlaceSeparateWitnessesPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ), 0 < r →
  ∀ (T Td T' Td' : CuspidalOperatorRealization F r),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : RP F) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' dd dd' : List RealBlock),
    T.realization.HasRealPlaceParameter v d →
    T'.realization.HasRealPlaceParameter v d' →
    Td.realization.HasRealPlaceParameter v dd →
    Td'.realization.HasRealPlaceParameter v dd' →
  ∃ D : RealQuotientMeasureData r, ∀ i : Bool,
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
        (if i then realEqualDualIntegral a D W W' Φ s else realEqualIntegral D W W' Φ s) ≠ 0

/-- The same separate witness condition at a complex place. -/
def ComplexEqualPlaceSeparateWitnessesPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ), 0 < r →
  ∀ (T Td T' Td' : CuspidalOperatorRealization F r),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (w : CP F) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' dd dd' : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d →
    T'.realization.HasComplexPlaceParameter w d' →
    Td.realization.HasComplexPlaceParameter w dd →
    Td'.realization.HasComplexPlaceParameter w dd' →
  ∃ D : ComplexQuotientMeasureData r, ∀ i : Bool,
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
        (if i then complexEqualDualIntegral a D W W' Φ s else complexEqualIntegral D W W' Φ s) ≠ 0

private theorem infiniteWhittakerSliceModel_of_identity
    (h : InfiniteWhittakerIdentityProportionalityPositiveRankStatement.{u, uQ}) :
    InfiniteWhittakerSliceModelPositiveRankStatement.{u, uQ} := by
  intro F _ _ _ r hr T P hI χ hχ dR hdR dC hdC
  obtain ⟨a₀, b₀, h₀⟩ := exists_tensorWhittaker_one_ne_zero P hI χ hχ
  exact nonempty_modelData_of_eval_one P hI χ hχ a₀ b₀ h₀
    (h F r hr T P hI χ hχ dR hdR dC hdC a₀ b₀ h₀)

private theorem realEqualPlaceTests_of_separate_witnesses
    (h : RealEqualPlaceSeparateWitnessesPositiveRankStatement.{u}) :
    RealEqualPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr T Td T' Td' hTd hTd' v a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨D, hD⟩ := h F ψ hψ r hr T Td T' Td' hTd hTd' v a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨W, W', Φ, hW, hW', h₀, h₁⟩ := EqualPlaceCommonTests.real ψ hψ T T' v a D
    (fun Φ hW hW' => realPlaceEqualPairConvergence ψ hψ T T' v a ha hd hd' D Φ hW hW') hD
  exact ⟨W, W', Φ, D, hW, hW', h₀, h₁⟩

private theorem complexEqualPlaceTests_of_separate_witnesses
    (h : ComplexEqualPlaceSeparateWitnessesPositiveRankStatement.{u}) :
    ComplexEqualPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨D, hD⟩ := h F ψ hψ r hr T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨W, W', Φ, hW, hW', h₀, h₁⟩ := EqualPlaceCommonTests.complex ψ hψ T T' w a D
    (fun Φ hW hW' => complexPlaceEqualPairConvergence ψ hψ T T' w a ha hd hd' D Φ hW hW') hD
  exact ⟨W, W', Φ, D, hW, hW', h₀, h₁⟩

/-- Identity comparison and separate real and complex local witnesses for `0 < r`
are sufficient for the published equal-rank conjunct. -/
def EqualWhittakerIdentityReductionStatement : Prop :=
  InfiniteWhittakerIdentityProportionalityPositiveRankStatement.{u, uQ} →
    RealEqualPlaceSeparateWitnessesPositiveRankStatement.{u} →
    ComplexEqualPlaceSeparateWitnessesPositiveRankStatement.{u} →
    EqualArchimedeanFactorizationStatement.{u, uQ}

theorem equalWhittakerIdentityReduction : EqualWhittakerIdentityReductionStatement.{u, uQ} :=
  fun hModel hR hC => equalWhittakerPositiveRankReduction
    (infiniteWhittakerSliceModel_of_identity hModel)
    (realEqualPlaceTests_of_separate_witnesses hR)
    (complexEqualPlaceTests_of_separate_witnesses hC)

end Langlands.Global.RankinSelbergGlobal
