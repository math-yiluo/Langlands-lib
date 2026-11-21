import Langlands.AllField.Representation.RankinSelberg.GammaMultiplicativityProof
import Langlands.AllField.Representation.RankinSelberg.FiniteLFactorMultiplicativity
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.AllField.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.RankinSelberg.RationalGammaExpressionProduct

/-! # The dual standard polynomial from the forward and epsilon products -/

noncomputable section

set_option autoImplicit false

namespace Langlands.AllField.RankinSelberg

open Polynomial Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.RankinSelberg (IsOfWhittakerType RationalFunctions succBlockShape
  rankOneCharacter rationalGammaExpression rationalEpsilonMonomial
  isOfWhittakerType_standard_iff_inverse isOfWhittakerType_firstDual)

universe uF uW

private theorem dual_injective_of_forward_nonzero
    (δ c : ℂˣ) (m : ℤ) {P : ℂ[X]} (hP : P ≠ 0) :
    Function.Injective (rationalGammaExpression δ c m P) := by
  intro D D' h
  apply RatFunc.algebraMap_injective ℂ
  apply (Langlands.LocalFactor.RationalReflection.equiv δ).injective
  change Langlands.LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) D) =
    Langlands.LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) D')
  rw [Langlands.LocalFactor.RationalReflection.subst_polynomial,
    Langlands.LocalFactor.RationalReflection.subst_polynomial]
  simp only [rationalGammaExpression, div_eq_mul_inv] at h
  exact inv_injective (mul_left_cancel₀ (mul_ne_zero (rationalEpsilonMonomial c m).ne_zero
    (RatFunc.algebraMap_ne_zero hP)) h)

private theorem standardGamma_of_symmetric {F : Type uF} [Field F] [TopologicalSpace F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : UnitaryAdditiveCharacter F)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances F) ψ)
    {t : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (t + 1) F) W)
    (one : Representation ℂ (GeneralLinear 1 F) ℂ)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (h₁ : IsOfWhittakerType 0 (standardCharacter ψ 0) one) {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν.val one π G → IsPadicPairGammaFactor F ψ ν.val π one G := by
  cases t with
  | zero =>
    exact ((isPadicSymmetricGammaFactor_of_le (Nat.le_refl 0)).trans
      (isPadicPairGammaFactor_swap_equalRank F ψ ν.val one π h₁ hπ G)).mp
  | succ t => exact (isPadicSymmetricGammaFactor_of_lt (Nat.succ_pos t)).mp

/-- If the standard epsilon and forward polynomial of the normalized product
are the corresponding block products, the actual inverse-transpose dual
polynomial is also the block product. -/
def StandardInductionDualPolynomialStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances F) ψ)
    (t k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    (W : Fin k → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)),
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∀ (e : Fin k → ℂˣ × ℤ) (P PD : Fin k → ℂ[X]),
    let one := rankOneCharacter (F := F) 1
    (∀ i, IsPadicPairEpsilonFactor F ψ ν.val (σ i) one (e i)) →
    (∀ i, IsPadicPairLPolynomial F ψ ν.val (σ i) one (P i)) →
    (∀ i, IsPadicPairLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback (σ i)) (inverseTransposePullback one) (PD i)) →
    let π := (LocalFieldData.ofInstances F).normalizedProductInduced (succBlockShape m h) σ
    IsPadicPairEpsilonFactor F ψ ν.val π one (∏ i, (e i).1, ∑ i, (e i).2) →
    IsPadicPairLPolynomial F ψ ν.val π one (∏ i, P i) →
    IsPadicPairLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback one) (∏ i, PD i)

set_option maxHeartbeats 4200000 in
theorem standardInductionDualPolynomial : StandardInductionDualPolynomialStatement.{uF, uW} := by
  classical
  intro F _ _ _ _ ψ ν t k m h W _ _ σ hσ e P PD one he hP hPD π hε hL
  have hone : IsOfWhittakerType 0 (standardCharacter ψ 0) one :=
    rankOneCharacter_isOfWhittakerType F ψ 1
  have hone' := (isOfWhittakerType_standard_iff_inverse ψ one).mp hone
  have hπ : IsOfWhittakerType t (standardCharacter ψ t) π :=
    normalizedProductWhittakerType F ψ t k m h σ hσ
  let νd := DominantRankTransport.negatedSelfDualHaar F ψ ν
  have hπd := isOfWhittakerType_firstDual ψ π hπ
  have honed := isOfWhittakerType_firstDual ψ one hone
  let D := whittakerTypeLPolynomial F (ψ.scale (-1)) νd _ _ hπd honed
  have hD : IsPadicPairLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback one) D :=
    (isPadicSymmetricLPolynomial_of_le (Nat.zero_le t)).mp
      (whittakerTypeLPolynomial_spec F (ψ.scale (-1)) νd _ _ hπd honed)
  obtain ⟨G, hG, hGprod⟩ := gammaMultiplicativity F ψ ν 0 t k m h one σ hone hσ
  let δ := LocalFactor.residueReflection F
  have hblock (i : Fin k) : G i = rationalGammaExpression δ (e i).1 (e i).2 (P i) (PD i) := by
    have hc := padicPairGammaConstructionInput_of_whittakerType F ψ ν (m i) 0 _ ℂ (σ i) one
      (Nat.zero_le _) (hσ i) hone'
    exact (standardGamma_of_symmetric ψ ν (σ i) one (hσ i) hone (hG i)).unique
      ((he i).gammaFactor_of_constructionInput F ψ ν.val (σ i) one hc (hP i) (hPD i))
  have hc := padicPairGammaConstructionInput_of_whittakerType F ψ ν t 0 _ ℂ π one
    (Nat.zero_le t) hπ hone'
  have hprod : (∏ i, G i) =
      rationalGammaExpression δ (∏ i, (e i).1) (∑ i, (e i).2) (∏ i, P i) D :=
    (standardGamma_of_symmetric ψ ν π one hπ hone hGprod).unique
      (IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val π one hc hε hL hD)
  simp_rw [hblock] at hprod
  rw [← Langlands.RankinSelberg.TemperedLFactorGamma.rationalGammaExpression_prod] at hprod
  have hP0 : (∏ i, P i) ≠ 0 := by
    intro h₀
    have hc₀ := hL.coeff_zero
    rw [h₀, Polynomial.coeff_zero] at hc₀
    exact zero_ne_one hc₀
  have hD_eq := dual_injective_of_forward_nonzero δ _ _ hP0 hprod
  rwa [hD_eq]

end Langlands.AllField.RankinSelberg
