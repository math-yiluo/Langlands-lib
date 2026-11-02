import Langlands.Representation.RankinSelberg.TemperedLFactorAlgebra
import Langlands.Representation.RankinSelberg.LFactorMultiplicativityProof
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof

/-! Two-family certified L-polynomials and a normalized residual quotient. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

namespace TemperedLFactorDivisibility

/-- Symmetric L certificates are invariant under exchanging the pair. -/
theorem symmetricLPolynomial_swap {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
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

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t k l : ℕ} (m : Fin k → ℕ) (n : Fin l → ℕ)
  (hm : ∑ i, (m i + 1) = r + 1) (hn : ∑ j, (n j + 1) = t + 1)
  {V : Fin k → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Fin l → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
  (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))
  (σ : ∀ j, Representation ℂ (Langlands.GeneralLinear (n j + 1) F.Carrier) (W j))

/-- Certificates for the actual inductions and every block pair, together with
one normalized residual dividing the double product by the induced polynomial. -/
structure TwoFamilyLPolynomialData where
  inducedPolynomial : ℂ[X]
  blockPolynomial : Fin k → Fin l → ℂ[X]
  induced_spec : IsPadicSymmetricLPolynomial F ψ ν.val
    (F.canonicalNormalizedProductInduced (succBlockShape m hm) π)
    (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ) inducedPolynomial
  block_spec : ∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val
    (π i) (σ j) (blockPolynomial i j)
  quotient : TemperedLFactorAlgebra.NormalizedPolynomialQuotient
    inducedPolynomial (∏ i, ∏ j, blockPolynomial i j)

/-- Apply published finite L-divisibility in both families and remove Laurent
powers using the normalization of every certificate. -/
theorem nonempty_twoFamilyLPolynomialData
    (hπ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
    (hσ : ∀ j, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j)) :
    Nonempty (TwoFamilyLPolynomialData F ψ ν m n hm hn π σ) := by
  classical
  have hσind := normalizedProductWhittakerType p F ψ t l n hn σ hσ
  obtain ⟨P, A, hP, hA, houter⟩ :=
    lFactorMultiplicativity p F ψ ν t r k m hm
      (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ) π hσind hπ
  have hP' := (symmetricLPolynomial_swap F ψ ν.val _ _ P).mp hP
  have hA' (i) := (symmetricLPolynomial_swap F ψ ν.val _ _ (A i)).mp (hA i)
  have hrows : ∀ i, ∃ Q : Fin l → ℂ[X],
      (∀ j, IsPadicSymmetricLPolynomial F ψ ν.val (π i) (σ j) (Q j)) ∧
      ∃ (R : ℂ[X]) (e : ℕ), X ^ e * ∏ j, Q j = R * A i := by
    intro i
    obtain ⟨B, Q, hB, hQ, hdiv⟩ :=
      lFactorMultiplicativity p F ψ ν (m i) t l n hn (π i) σ (hπ i) hσ
    have hBA : B = A i := hB.unique (hA' i)
    exact ⟨Q, hQ, by simpa only [hBA] using hdiv⟩
  choose Q hQ hinner using hrows
  exact ⟨{
    inducedPolynomial := P
    blockPolynomial := Q
    induced_spec := hP'
    block_spec := hQ
    quotient := TemperedLFactorAlgebra.NormalizedPolynomialQuotient.of_doubleProduct
      (IsPadicSymmetricLPolynomial.coeff_zero hP')
      (fun i => IsPadicSymmetricLPolynomial.coeff_zero (hA' i))
      (fun i j => IsPadicSymmetricLPolynomial.coeff_zero (hQ i j))
      houter hinner }⟩

/-- Choose the two-family certificates and residual from full Whittaker-type
blocks, without assuming square integrability or a pole bound. -/
def twoFamilyLPolynomialData
    (hπ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
    (hσ : ∀ j, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j)) :
    TwoFamilyLPolynomialData F ψ ν m n hm hn π σ :=
  Classical.choice (nonempty_twoFamilyLPolynomialData F ψ ν m n hm hn π σ hπ hσ)

end Families

end TemperedLFactorDivisibility

end Langlands.RankinSelberg
