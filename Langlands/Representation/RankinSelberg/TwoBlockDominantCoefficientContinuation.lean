import Langlands.Representation.RankinSelberg.TwoBlockDominantRationalNumerators
import Langlands.Representation.RankinSelberg.UnequalRankDeterminantSlices
import Langlands.Representation.RankinSelberg.AnalyticBridge

/-!
# Actual model coefficient clearing and denominator bounds

Convergence is taken from the actual intrinsic zeta-value witnesses. Full
Whittaker type identifies those coefficients with any fixed nonzero models.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance coefficientContinuationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance coefficientContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance coefficientContinuationQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance coefficientContinuationMatrixMeasurable (j n : ℕ) :
    MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier) := borel _
local instance coefficientContinuationMatrixBorel (j n : ℕ) :
    BorelSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Equal

variable (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W)
  (ell : glFunctionals ψ n π) (ell' : glInverseFunctionals ψ n τ)

/-- Every pair of coefficients in the fixed models, with every actual row
test, has a finite numerator for the specified ordinary clearing polynomial. -/
def EqualModelFiniteClearing (A : Polynomial ℂ) : Prop :=
  ∀ (f : (coefficientModel π ell).toSubmodule)
    (f' : (coefficientModel τ ell').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient F.canonicalTopologicalData μ ψ f.val f'.val Φ
    ∃ N : LaurentPolynomial ℂ, ofLaurentPolynomial N = A.toLaurent • a

/-- The actual equal-rank coefficient expansion on a right half-plane. -/
theorem equalRank_hasBilateralSpectralExpansion
    (U : WhittakerFunctions ψ n) (U' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
    (hconv : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      EqualRankConverges ψ abv μ U U' Φ s) :
    HasBilateralSpectralExpansion qF
      (equalRankSliceCoefficient F.canonicalTopologicalData μ ψ U U' Φ)
      (fun s => equalRankIntegral ψ abv μ U U' Φ s) := by
  obtain ⟨C, hC⟩ := hconv
  exact ⟨C, fun s hs =>
    (equalRankSliceExpansion F F.canonicalTopologicalData n μ ψ U U' Φ s
      (hC s hs)).2.2⟩

/-- Finite clearing on one nonzero model pair controls every intrinsic equal
rank zeta value and yields the required polynomial divisibility direction. -/
theorem equalModelFiniteClearing_polynomialDivisibility
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hτ : IsOfWhittakerType n (inverseStandardCharacter ψ n) τ)
    (hell : ell.val ≠ 0) (hell' : ell'.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsEqualRankLPolynomial qF ψ abv μ π τ P)
    (hclear : EqualModelFiniteClearing F ψ μ π τ ell ell' A) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  apply normalizedGenerator_divisibility_of_clearedExpansions
    F.canonicalTopologicalData.residueCardinality_gt_one
    (equalRankZetaValues qF ψ abv μ π τ) P A hP hA
  intro R hR
  rw [equalRankZetaValues_eq_model qF ψ abv μ ell ell'
    (hπ.eq_smul hell) (hτ.eq_smul hell')] at hR
  obtain ⟨U, hU, U', hU', Φ, hconv, hcont⟩ := hR
  exact ⟨equalRankSliceCoefficient F.canonicalTopologicalData μ ψ U U' Φ,
    fun s => equalRankIntegral ψ abv μ U U' Φ s,
    equalRank_hasBilateralSpectralExpansion F ψ μ U U' Φ hconv,
    hcont, hclear ⟨U, hU⟩ ⟨U', hU'⟩ Φ⟩

end Equal

section Strict

variable (j k : ℕ)
  (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
  (π : Representation ℂ (GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W)
  (ell : glFunctionals ψ (n + (j + k + 1)) π)
  (ell' : glInverseFunctionals ψ n τ)

/-- The actual unequal-rank determinant coefficients in the specified models
have finite numerators after multiplying by the given polynomial. -/
def StrictModelFiniteClearing (A : Polynomial ℂ) : Prop :=
  ∀ (f : (coefficientModel π ell).toSubmodule)
    (f' : (coefficientModel τ ell').toSubmodule),
    let a : BilateralLaurentSeries :=
      unequalRankSliceCoefficient F j k ψ μ ν f.val f'.val
    ∃ N : LaurentPolynomial ℂ, ofLaurentPolynomial N = A.toLaurent • a

/-- Product-space absolute convergence gives the actual unequal-rank spectral
expansion on that same right half-plane. -/
theorem unequalRank_hasBilateralSpectralExpansion [SFinite ν]
    (U : WhittakerFunctions ψ (n + (j + k + 1)))
    (U' : InverseWhittakerFunctions ψ n)
    (hconv : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      UnequalRankConverges ψ abv j k μ ν U U' s) :
    HasBilateralSpectralExpansion qF
      (unequalRankSliceCoefficient F j k ψ μ ν U U')
      (fun s => unequalRankIntegral ψ abv j k μ ν U U' s) := by
  obtain ⟨C, hC⟩ := hconv
  exact ⟨C, fun s hs =>
    (unequalRankSliceExpansion_of_converges F j k ψ μ ν U U' s
      (hC s hs)).2.2⟩

/-- A uniform finite clearing on fixed nonzero models controls the complete
intrinsic unequal-rank L polynomial. No new convergence assumption is needed. -/
theorem strictModelFiniteClearing_polynomialDivisibility [SFinite ν]
    (hπ : IsOfWhittakerType (n + (j + k + 1))
      (standardCharacter ψ (n + (j + k + 1))) π)
    (hτ : IsOfWhittakerType n (inverseStandardCharacter ψ n) τ)
    (hell : ell.val ≠ 0) (hell' : ell'.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsUnequalRankLPolynomial qF ψ abv j k μ ν π τ P)
    (hclear : StrictModelFiniteClearing F ψ μ j k ν π τ ell ell' A) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  apply normalizedGenerator_divisibility_of_clearedExpansions
    F.canonicalTopologicalData.residueCardinality_gt_one
    (unequalRankZetaValues qF ψ abv j k μ ν π τ) P A hP hA
  intro R hR
  rw [unequalRankZetaValues_eq_model qF ψ abv j k μ ν ell ell'
    (hπ.eq_smul hell) (hτ.eq_smul hell')] at hR
  obtain ⟨U, hU, U', hU', hconv, hcont⟩ := hR
  exact ⟨unequalRankSliceCoefficient F j k ψ μ ν U U',
    fun s => unequalRankIntegral ψ abv j k μ ν U U' s,
    unequalRank_hasBilateralSpectralExpansion F ψ μ j k ν U U' hconv,
    hcont, hclear ⟨U, hU⟩ ⟨U', hU'⟩⟩

end Strict

end Langlands.RankinSelberg.DominantRankTransport
