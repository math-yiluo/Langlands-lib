import Langlands.Global.RankinSelberg.RealPlaceAnalyticReduction
import Langlands.Global.RankinSelberg.RealEqualRankZeroReduction
import Langlands.LocalFactor.Archimedean.RealTateProof

/-! # Real-place reduction with the rank-one equal case discharged -/

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

/-- The equal-rank real-place equation for GL₁ × GL₁ follows from the proved Tate theory. -/
theorem realEqualAtRank_zero : RealEqualAtRankStatement.{u} 0 :=
  realEqualAtRankStatement_zero Langlands.LocalFactor.RealTate.realArchimedeanTateStatement

/-- The source-convention analytic equations, with equal rank index restricted to r > 0. -/
def RealPositiveJacquetRestrictionEquationStatement : Prop :=
  (by
    classical
    exact
    ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
      (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
    ∀ (r t : ℕ) (h : t < r) (T Td : Automorphic.CuspidalOperatorRealization F r)
      (T' Td' : Automorphic.CuspidalOperatorRealization F t),
      Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
      Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
    ∀ (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
      IsRealAdditiveComponent ψ v.1 v.2 a →
    ∀ (d d' dd dd' : List RealBlock),
      Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v d →
      Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v d' →
      Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v dd →
      Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v dd' →
    ∀ (D : RealQuotientMeasureData t)
      (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
      IsRealPlaceWhittaker F T ψ.complex v W →
      IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' →
    RealJacquet.UnequalEquation h a D W W' d d' dd dd' (-a)
      (realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v)) ∧
  (by
    classical
    exact
    ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
      (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
    ∀ (r : ℕ), 0 < r →
    ∀ (T Td T' Td' : Automorphic.CuspidalOperatorRealization F r),
      Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
      Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
    ∀ (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
      IsRealAdditiveComponent ψ v.1 v.2 a →
    ∀ (d d' dd dd' : List RealBlock),
      Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v d →
      Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v d' →
      Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v dd →
      Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v dd' →
    ∀ (D : RealQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
      IsRealPlaceWhittaker F T ψ.complex v W →
      IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' →
    RealJacquet.EqualEquation a (-a) D W W' Φ d d' dd dd'
      (realMinusOneScalar T v ^ r))

/-- The remaining analytic equations imply the exact real-place target; GL₁ × GL₁ is proved. -/
def RealPlacePositiveAnalyticReductionStatement : Prop :=
  RealPositiveJacquetRestrictionEquationStatement.{u} →
  RealPlaceFunctionalEquationStatement.{u}

theorem realPlacePositiveAnalyticReduction : RealPlacePositiveAnalyticReductionStatement.{u} := by
  intro hJ
  have hC := realPairCentralCompatibility_of_standardNonzero realStandardKFiniteNonzero
  have hR := realEqualDualReflection
  constructor
  · intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' hW hW'
    change RealJacquet.UnequalEquation h a D W W' d d' dd dd' a
      (realMinusOneScalar T' v ^ r)
    have hEq := hJ.1 F ψ hψ r t h T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' hW hW'
    apply RealJacquet.EquationPackage.change_factor hEq
    intro s
    rw [RealJacquet.pair_epsilon_neg, hC F r t T T' v d d' hd hd']
    calc
      _ = ((realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v) *
          (realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v ^ (r + 1))) *
          (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) := by ring
      _ = _ := by rw [RealJacquet.unequal_sign _ _
        (realMinusOneScalar_sq T v) (realMinusOneScalar_sq T' v)]
  · intro F _ _ _ ψ hψ r T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
    by_cases hr : r = 0
    · subst r
      exact realEqualAtRank_zero F ψ hψ T Td T' Td' hTd hTd' v a hA
        d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
    ·
      change RealJacquet.EqualEquation a a D W W' Φ d d' dd dd'
        (realMinusOneScalar T' v ^ r)
      have hEq := hJ.2 F ψ hψ r (Nat.pos_of_ne_zero hr) T Td T' Td' hTd hTd' v a hA
        d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
      obtain ⟨hK, hZ⟩ := hR F ψ hψ r T Td T' Td' hTd hTd' v a hA
        d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
      have hk : (realMinusOneScalar T v * realMinusOneScalar T' v) ^ 2 = 1 := by
        rw [mul_pow, realMinusOneScalar_sq T v, realMinusOneScalar_sq T' v, one_mul]
      have hEp := RealJacquet.EquationPackage.reflect_dual hk hK hZ hEq
      apply RealJacquet.EquationPackage.change_factor hEp
      intro s
      rw [RealJacquet.pair_epsilon_neg, hC F r r T T' v d d' hd hd']
      calc
        _ = ((realMinusOneScalar T v * realMinusOneScalar T' v) *
            (realMinusOneScalar T v ^ r *
              (realMinusOneScalar T v ^ (r + 1) * realMinusOneScalar T' v ^ (r + 1)))) *
            (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) := by ring
        _ = _ := by rw [RealJacquet.equal_sign _ _
          (realMinusOneScalar_sq T v) (realMinusOneScalar_sq T' v)]


end Langlands.Global.RankinSelbergGlobal
