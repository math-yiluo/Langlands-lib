import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerSliceReduction
import Langlands.Global.RankinSelberg.RankOneWhittakerSlice
import Langlands.Global.RankinSelberg.ComplexRankZeroTests
import Langlands.LocalFactor.Archimedean.ComplexTateProof

/-! # Equal-rank factorization with local tests in ranks above one -/

noncomputable section
universe u uQ

open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic InfinitePlaceFamily
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.Global.HeckeFunctionalEquation
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal
open InfiniteWhittakerSlice

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- The local slice comparison for groups `GL_(r+1)` with `0 < r`. -/
def InfiniteWhittakerSliceModelPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
  ∀ (r : ℕ), 0 < r →
  ∀ (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hI : HasIrreducibleAdmissibleComponents P)
    (χ : AddChar (Adeles F) ℂ),
    IsStandardAdditiveCharacter F χ →
  ∀ (dR : (RP F) → List RealBlock),
    (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
  ∀ (dC : (CP F) → List ComplexCharacterData),
    (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    Nonempty (ModelData P hI χ)

/-- The real place tests for pairs of groups `GL_(r+1)` with `0 < r`. -/
def RealEqualPlaceTestsPositiveRankStatement : Prop :=
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
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ) (D : RealQuotientMeasureData r),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) ∧
      HolomorphicNonzeroOnRightHalfPlane (realEqualDualIntegral a D W W' Φ)

/-- The complex place tests for pairs of groups `GL_(r+1)` with `0 < r`. -/
def ComplexEqualPlaceTestsPositiveRankStatement : Prop :=
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
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) (D : ComplexQuotientMeasureData r),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) ∧
      HolomorphicNonzeroOnRightHalfPlane (complexEqualDualIntegral a D W W' Φ)

private theorem infiniteWhittakerSliceModel_of_positive
    (h : InfiniteWhittakerSliceModelPositiveRankStatement.{u, uQ}) :
    InfiniteWhittakerSliceModelStatement.{u, uQ} := by
  intro F _ _ _ r
  cases r with
  | zero =>
    intro T P hI χ _ _ _ _ _
    exact rankOneWhittakerSlice F T P hI χ
  | succ r => exact h F r.succ (Nat.succ_pos r)

private theorem realEqualPlaceTests_of_positive (h : RealEqualPlaceTestsPositiveRankStatement.{u}) :
    RealEqualPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r
  cases r with
  | zero =>
    intro T Td T' Td' hTd hTd' v a _ d d' dd dd' hd hd' hdd hdd'
    exact RealRankZero.realEqual_rankZero_tests_exists ψ.complex T Td T' Td' hTd hTd'
      v a d d' dd dd' hd hd' hdd hdd'
  | succ r => exact h F ψ hψ r.succ (Nat.succ_pos r)

/-- Combine the positive-rank complex tests with the rank-one Tate tests. -/
theorem complexEqualPlaceTests_of_positive (h : ComplexEqualPlaceTestsPositiveRankStatement.{u}) :
    ComplexEqualPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r
  cases r with
  | zero =>
    intro T _ T' _ _ _ w a ha d d' _ _ hd hd' _ _
    exact ComplexRankZero.complexEqual_rankZero_tests_exists
      ComplexTate.complexArchimedeanTateStatement ψ hψ T T' w a ha d d' hd hd'
  | succ r => exact h F ψ hψ r.succ (Nat.succ_pos r)

/-- Rank one follows from the two Tate theories and central-character covariance.
The other ranks retain precisely their local slice and test inputs. -/
def EqualWhittakerPositiveRankReductionStatement : Prop :=
  InfiniteWhittakerSliceModelPositiveRankStatement.{u, uQ} →
    RealEqualPlaceTestsPositiveRankStatement.{u} → ComplexEqualPlaceTestsPositiveRankStatement.{u} →
    EqualArchimedeanFactorizationStatement.{u, uQ}

/-- The three rank-restricted inputs give the exact equal-rank factorization
by the local comparison reduction. -/
theorem equalWhittakerPositiveRankReduction : EqualWhittakerPositiveRankReductionStatement.{u, uQ} :=
  fun hModel hR hC => equalInfiniteWhittakerSliceReduction
    (infiniteWhittakerSliceModel_of_positive hModel)
    (realEqualPlaceTests_of_positive hR) (complexEqualPlaceTests_of_positive hC)

end Langlands.Global.RankinSelbergGlobal
