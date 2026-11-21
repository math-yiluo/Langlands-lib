import Langlands.AllField.Representation.RankinSelberg.GammaMultiplicativityProof
import Langlands.AllField.Representation.RankinSelberg.LFactorMultiplicativityProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankSwapFactors
import Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.AllField.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.RankinSelberg.RationalGammaExpressionProduct
import Langlands.Representation.RankinSelberg.SeparatedGammaProduct
import Langlands.Representation.RankinSelberg.TemperedLFactorAlgebra

noncomputable section

namespace Langlands.AllField.RankinSelberg

open Polynomial Langlands.HarmonicAnalysis Langlands.Whittaker Langlands.GeneralLinear
open Langlands.RankinSelberg (IsOfWhittakerType RationalFunctions succBlockShape
  rankOneCharacter rationalGammaExpression isOfWhittakerType_standard_iff_inverse
  isOfWhittakerType_firstDual eq_of_separated_rationalGammaExpression)
open Langlands.RankinSelberg.TemperedLFactorAlgebra (normalizedQuotient_of_laurentDivisibility)

universe uF uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]

private theorem standardTestLPolynomial_iff
    (ψ : UnitaryAdditiveCharacter F) (ν : LocalFactor.PadicAbelian.SelfDualHaar
      (⟨⟩ : LocalFieldData F) ψ) {s : ℕ} {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (s + 1) F) V)
    (one : Representation ℂ (GeneralLinear 1 F) ℂ) (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν.val one π P ↔
      IsPadicPairLPolynomial F ψ ν.val π one P := by
  cases s with
  | zero =>
    exact (isPadicSymmetricLPolynomial_of_le (le_refl 0)).trans
      (isPadicPairLPolynomial_swap_equalRank F ψ ν.val one π P)
  | succ s => exact isPadicSymmetricLPolynomial_of_lt (Nat.succ_pos s)

private theorem standardTestGamma_iff
    (ψ : UnitaryAdditiveCharacter F) (ν : LocalFactor.PadicAbelian.SelfDualHaar
      (⟨⟩ : LocalFieldData F) ψ) {s : ℕ} {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (s + 1) F) V)
    (one : Representation ℂ (GeneralLinear 1 F) ℂ)
    (hπ : IsOfWhittakerType s (standardCharacter ψ s) π)
    (hone : IsOfWhittakerType 0 (standardCharacter ψ 0) one)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ ν.val one π G ↔
      IsPadicPairGammaFactor F ψ ν.val π one G := by
  cases s with
  | zero =>
    exact (isPadicSymmetricGammaFactor_of_le (le_refl 0)).trans
      (isPadicPairGammaFactor_swap_equalRank F ψ ν.val one π hone hπ G)
  | succ s => exact isPadicSymmetricGammaFactor_of_lt (Nat.succ_pos s)

set_option maxHeartbeats 800000 in
/-- If the block L-polynomials and the reflected dual block product have no
common nonzero root, the standard epsilon monomial and the standard L-polynomial
of the normalized induction are the respective products. -/
theorem separatedStandardFactorProduct
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F) (ν : LocalFactor.PadicAbelian.SelfDualHaar
      (⟨⟩ : LocalFieldData F) ψ)
    {t k : ℕ} (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (e : Fin k → ℂˣ × ℤ) (P PD : Fin k → ℂ[X])
    (he : ∀ i, IsPadicPairEpsilonFactor F ψ ν.val (σ i) (rankOneCharacter 1) (e i))
    (hP : ∀ i, IsPadicPairLPolynomial F ψ ν.val (σ i) (rankOneCharacter 1) (P i))
    (hPD : ∀ i, IsPadicPairLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback (σ i)) (inverseTransposePullback (rankOneCharacter 1)) (PD i))
    (hsep : ∀ x : ℂ, x ≠ 0 → (∏ i, P i).eval x = 0 →
      (∏ i, PD i).eval ((LocalFactor.residueReflection F : ℂˣ) / x) ≠ 0) :
    let π := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ
    IsPadicPairEpsilonFactor F ψ ν.val π (rankOneCharacter 1)
      (∏ i, (e i).1, ∑ i, (e i).2) ∧
    IsPadicPairLPolynomial F ψ ν.val π (rankOneCharacter 1) (∏ i, P i) := by
  classical
  let := (⟨⟩ : LocalFieldData F).topology
  let one := rankOneCharacter (F := F) 1
  let π := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ
  change IsPadicPairEpsilonFactor F ψ ν.val π one (∏ i, (e i).1, ∑ i, (e i).2) ∧
    IsPadicPairLPolynomial F ψ ν.val π one (∏ i, P i)
  have hone : IsOfWhittakerType 0 (standardCharacter ψ 0) one :=
    rankOneCharacter_isOfWhittakerType F ψ 1
  have hone' := (isOfWhittakerType_standard_iff_inverse ψ one).mp hone
  have hπ : IsOfWhittakerType t (standardCharacter ψ t) π :=
    normalizedProductWhittakerType F ψ t k m h σ hσ
  have hcin := padicPairGammaConstructionInput_of_whittakerType F ψ ν t 0 _ ℂ π one
    (Nat.zero_le t) hπ hone'
  obtain ⟨e₀, he₀⟩ := hcin.2.2.1
  obtain ⟨P₀, Pi, hP₀s, hPi, R, a, hdiv⟩ :=
    lFactorMultiplicativity F ψ ν 0 t k m h one σ hone hσ
  have hP₀ : IsPadicPairLPolynomial F ψ ν.val π one P₀ :=
    (standardTestLPolynomial_iff ψ ν π one P₀).mp hP₀s
  have hPi_eq (i : Fin k) : Pi i = P i :=
    ((standardTestLPolynomial_iff ψ ν (σ i) one (Pi i)).mp (hPi i)).unique (hP i)
  simp_rw [hPi_eq] at hdiv
  have hPprod : (∏ i, P i).coeff 0 = 1 := by
    simp [coeff_zero_prod, fun i => (hP i).coeff_zero]
  have hPDprod : (∏ i, PD i).coeff 0 = 1 := by
    simp [coeff_zero_prod, fun i => (hPD i).coeff_zero]
  obtain ⟨Q, hQ, hQeq⟩ := normalizedQuotient_of_laurentDivisibility
    hP₀.coeff_zero hPprod hdiv
  let νd := DominantRankTransport.negatedSelfDualHaar F ψ ν
  have hπd := isOfWhittakerType_firstDual ψ π hπ
  have honed := isOfWhittakerType_firstDual ψ one hone
  let D := whittakerTypeLPolynomial F (ψ.scale (-1)) νd _ _ hπd honed
  have hD : IsPadicPairLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback one) D :=
    (isPadicSymmetricLPolynomial_of_le (Nat.zero_le t)).mp
      (whittakerTypeLPolynomial_spec F (ψ.scale (-1)) νd _ _ hπd honed)
  obtain ⟨G, hG, hind⟩ := gammaMultiplicativity F ψ ν 0 t k m h one σ hone hσ
  let δ := LocalFactor.residueReflection F
  have hGi (i : Fin k) : G i = rationalGammaExpression δ (e i).1 (e i).2 (P i) (PD i) := by
    have hc := padicPairGammaConstructionInput_of_whittakerType F ψ ν (m i) 0 _ ℂ (σ i) one
      (Nat.zero_le _) (hσ i) hone'
    exact ((standardTestGamma_iff ψ ν (σ i) one (hσ i) hone (G i)).mp (hG i)).unique
      ((he i).gammaFactor_of_constructionInput F ψ ν.val (σ i) one hc (hP i) (hPD i))
  have hGi_prod : (∏ i, G i) = rationalGammaExpression δ e₀.1 e₀.2 P₀ D :=
    ((standardTestGamma_iff ψ ν π one hπ hone _).mp hind).unique
      (IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val π one hcin he₀ hP₀ hD)
  have hgamma : rationalGammaExpression δ (∏ i, (e i).1) (∑ i, (e i).2)
      (∏ i, P i) (∏ i, PD i) = rationalGammaExpression δ e₀.1 e₀.2 P₀ D := by
    rw [Langlands.RankinSelberg.TemperedLFactorGamma.rationalGammaExpression_prod]
    simpa only [hGi] using hGi_prod
  obtain ⟨hL, hε⟩ := eq_of_separated_rationalGammaExpression
    (e := e₀) (e' := (∏ i, (e i).1, ∑ i, (e i).2))
    hP₀.coeff_zero hD.coeff_zero hPDprod hQ hQeq hsep hgamma
  exact ⟨hε ▸ he₀, hL ▸ hP₀⟩

end Langlands.AllField.RankinSelberg
