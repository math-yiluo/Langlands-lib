import Langlands.Representation.RankinSelberg.TemperedLFactorDivisibility
import Langlands.AllField.Representation.RankinSelberg.LFactorMultiplicativityProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.PadicPairLPolynomialNormalization

/-!
# Two-family certified L-polynomials and a normalized residual quotient

For two families of blocks of Whittaker type over a nonarchimedean local field, JPSS
1983, Theorem (3.1)(ii) (printed pages 404-405), applied in both families, gives the
L-polynomial `P` of the two normalized products, the L-polynomials `Q i j` of the
block pairs, and a normalized polynomial `D` with `∏ i, ∏ j, Q i j = D * P`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

namespace TemperedLFactorDivisibility

/-- Symmetric L certificates are invariant under exchanging the pair. -/
theorem symmetricLPolynomial_swap
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F) (ν : letI := borel F; AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν π σ P ↔
      IsPadicSymmetricLPolynomial F ψ ν σ π P := by
  rcases lt_trichotomy r n with h | h | h
  · simp only [IsPadicSymmetricLPolynomial, Nat.not_le.mpr h,
      Nat.le_of_lt h, ↓reduceIte]
  · subst n
    simpa only [IsPadicSymmetricLPolynomial, le_refl, ↓reduceIte] using
      isPadicPairLPolynomial_swap_equalRank F ψ ν π σ P
  · simp only [IsPadicSymmetricLPolynomial, Nat.not_le.mpr h,
      Nat.le_of_lt h, ↓reduceIte]

section Families

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {r t k l : ℕ} (m : Fin k → ℕ) (n : Fin l → ℕ)
  (hm : ∑ i, (m i + 1) = r + 1) (hn : ∑ j, (n j + 1) = t + 1)
  {V : Fin k → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Fin l → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
  (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (V i))
  (σ : ∀ j, Representation ℂ (Langlands.GeneralLinear (n j + 1) F) (W j))

/-- Certificates for the actual inductions and every block pair, together with
one normalized residual dividing the double product by the induced polynomial. -/
structure TwoFamilyLPolynomialData where
  inducedPolynomial : ℂ[X]
  blockPolynomial : Fin k → Fin l → ℂ[X]
  induced_spec : IsPadicSymmetricLPolynomial F ψ ν.val
    ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m hm) π)
    ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape n hn) σ)
    inducedPolynomial
  block_spec : ∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val
    (π i) (σ j) (blockPolynomial i j)
  quotient : Langlands.RankinSelberg.TemperedLFactorAlgebra.NormalizedPolynomialQuotient
    inducedPolynomial (∏ i, ∏ j, blockPolynomial i j)

/-- Apply finite L-divisibility in both families and remove Laurent powers using
the normalization of every certificate. -/
theorem nonempty_twoFamilyLPolynomialData
    (hπ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
    (hσ : ∀ j, IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j)) :
    Nonempty (TwoFamilyLPolynomialData F ψ ν m n hm hn π σ) := by
  classical
  have hσind := normalizedProductWhittakerType F ψ t l n hn σ hσ
  obtain ⟨P, A, hP, hA, houter⟩ :=
    lFactorMultiplicativity F ψ ν t r k m hm
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape n hn) σ) π hσind hπ
  have hP' := (symmetricLPolynomial_swap F ψ ν.val _ _ P).mp hP
  have hA' (i) := (symmetricLPolynomial_swap F ψ ν.val _ _ (A i)).mp (hA i)
  have hrows : ∀ i, ∃ Q : Fin l → ℂ[X],
      (∀ j, IsPadicSymmetricLPolynomial F ψ ν.val (π i) (σ j) (Q j)) ∧
      ∃ (R : ℂ[X]) (e : ℕ), X ^ e * ∏ j, Q j = R * A i := by
    intro i
    obtain ⟨B, Q, hB, hQ, hdiv⟩ :=
      lFactorMultiplicativity F ψ ν (m i) t l n hn (π i) σ (hπ i) hσ
    have hBA : B = A i := hB.unique (hA' i)
    exact ⟨Q, hQ, by simpa only [hBA] using hdiv⟩
  choose Q hQ hinner using hrows
  exact ⟨{
    inducedPolynomial := P
    blockPolynomial := Q
    induced_spec := hP'
    block_spec := hQ
    quotient :=
      Langlands.RankinSelberg.TemperedLFactorAlgebra.NormalizedPolynomialQuotient.of_doubleProduct
        (IsPadicSymmetricLPolynomial.coeff_zero hP')
        (fun i => IsPadicSymmetricLPolynomial.coeff_zero (hA' i))
        (fun i j => IsPadicSymmetricLPolynomial.coeff_zero (hQ i j))
        houter hinner }⟩

/-- Choose the two-family certificates and residual from blocks of Whittaker type,
without assuming square integrability or a pole bound. -/
def twoFamilyLPolynomialData
    (hπ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
    (hσ : ∀ j, IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j)) :
    TwoFamilyLPolynomialData F ψ ν m n hm hn π σ :=
  Classical.choice (nonempty_twoFamilyLPolynomialData F ψ ν m n hm hn π σ hπ hσ)

end Families

end TemperedLFactorDivisibility

end Langlands.AllField.RankinSelberg
