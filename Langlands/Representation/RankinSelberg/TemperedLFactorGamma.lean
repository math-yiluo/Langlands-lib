import Langlands.Representation.RankinSelberg.TemperedLFactorDivisibility
import Langlands.Representation.RankinSelberg.GammaMultiplicativityProof
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof

/-! Gamma assembly for two full Whittaker-type block families. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

namespace TemperedLFactorGamma

/-- Extract the certified epsilon data already present in the closed
Whittaker-type construction input, in either rank order. -/
theorem epsilon_exists_of_whittakerType {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ e : ℂˣ × ℤ, IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e := by
  have h := whittakerTypeGammaConstructionInput p F ψ ν r n V W π σ hπ hσ
  by_cases hnr : n ≤ r
  · have ho : PadicPairGammaConstructionInput F ψ ν.val π σ := by
      simpa only [PadicSymmetricGammaConstructionInput, hnr, ↓reduceIte] using h
    obtain ⟨e, he⟩ := ho.2.2.1
    exact ⟨e, (isPadicSymmetricEpsilonFactor_of_le hnr).mpr he⟩
  · have ho : PadicPairGammaConstructionInput F ψ ν.val σ π := by
      simpa only [PadicSymmetricGammaConstructionInput, hnr, ↓reduceIte] using h
    obtain ⟨e, he⟩ := ho.2.2.1
    exact ⟨e, (isPadicSymmetricEpsilonFactor_of_lt (Nat.lt_of_not_ge hnr)).mpr he⟩

/-- Fixed-character symmetric gamma exchange for full-type representations. -/
theorem symmetricGammaFactor_swap {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) σ)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ ν π σ G ↔
      IsPadicSymmetricGammaFactor F ψ ν σ π G := by
  rcases lt_trichotomy r n with h | h | h
  · simp only [IsPadicSymmetricGammaFactor, Nat.not_le.mpr h,
      Nat.le_of_lt h, ↓reduceIte]
  · subst n
    simpa only [IsPadicSymmetricGammaFactor, le_refl, ↓reduceIte] using
      isPadicPairGammaFactor_swap_equalRank F ψ ν π σ hπ hσ G
  · simp only [IsPadicSymmetricGammaFactor, Nat.not_le.mpr h,
      Nat.le_of_lt h, ↓reduceIte]

/-- The explicit gamma expression multiplies over any finite index type. -/
theorem rationalGammaExpression_prod {ι : Type*} [Fintype ι]
    (δ : ℂˣ) (P PD : ι → ℂ[X]) (c : ι → ℂˣ) (a : ι → ℤ) :
    rationalGammaExpression δ (∏ i, c i) (∑ i, a i) (∏ i, P i) (∏ i, PD i) =
      ∏ i, rationalGammaExpression δ (c i) (a i) (P i) (PD i) := by
  classical
  have hz (s : Finset ι) :
      (RatFunc.X : RationalFunctions) ^ (∑ i ∈ s, a i) =
        ∏ i ∈ s, (RatFunc.X : RationalFunctions) ^ a i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        zpow_add₀ (show (RatFunc.X : RationalFunctions) ≠ 0 from RatFunc.X_ne_zero), ih]
  simp only [rationalGammaExpression, coe_rationalEpsilonMonomial,
    map_prod, Units.coe_prod, Finset.prod_div_distrib, Finset.prod_mul_distrib, hz]

/-- An explicit Laurent monomial relating the original and reflected ratios. -/
structure ReflectedRatioData (δ : ℂˣ) (P PD B BD : ℂ[X]) where
  coefficient : ℂˣ
  exponent : ℤ
  ratio : algebraMap ℂ[X] RationalFunctions B /
      LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions BD) =
    (RatFunc.C (coefficient : ℂ) * (RatFunc.X : RationalFunctions) ^ exponent) *
      algebraMap ℂ[X] RationalFunctions P /
        LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions PD)

/-- Cancel the nonzero product epsilon monomial from two gamma expressions. -/
theorem reflectedRatio_of_gammaExpression_eq
    (δ c₀ c₁ : ℂˣ) (a₀ a₁ : ℤ) (P PD B BD : ℂ[X])
    (h : rationalGammaExpression δ c₁ a₁ B BD =
      rationalGammaExpression δ c₀ a₀ P PD) :
    algebraMap ℂ[X] RationalFunctions B /
        LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions BD) =
      (RatFunc.C ((c₀ / c₁ : ℂˣ) : ℂ) *
        (RatFunc.X : RationalFunctions) ^ (a₀ - a₁)) *
          algebraMap ℂ[X] RationalFunctions P /
            LocalFactor.RationalReflection.subst δ
              (algebraMap ℂ[X] RationalFunctions PD) := by
  have hmon :
      (rationalEpsilonMonomial (c₀ / c₁) (a₀ - a₁) : RationalFunctions) =
        (rationalEpsilonMonomial c₀ a₀ : RationalFunctions) /
          (rationalEpsilonMonomial c₁ a₁ : RationalFunctions) := by
    simp only [coe_rationalEpsilonMonomial, Units.val_div_eq_div_val, map_div₀,
      zpow_sub₀ (show (RatFunc.X : RationalFunctions) ≠ 0 from RatFunc.X_ne_zero)]
    ring
  rw [← RatFunc.algebraMap_eq_C, ← coe_rationalEpsilonMonomial, hmon]
  apply mul_left_cancel₀ (rationalEpsilonMonomial c₁ a₁).ne_zero
  calc
    _ = rationalGammaExpression δ c₁ a₁ B BD := by
      simp only [rationalGammaExpression, LocalFactor.RationalReflection.subst_polynomial]
      ring
    _ = rationalGammaExpression δ c₀ a₀ P PD := h
    _ = _ := by
      simp only [rationalGammaExpression, LocalFactor.RationalReflection.subst_polynomial]
      field_simp
      exact (mul_div_mul_right _ _ (rationalEpsilonMonomial c₁ a₁).ne_zero).symm

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
  (hπ : ∀ i, letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
  (hσ : ∀ j, letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j))

include hπ hσ in
/-- Published gamma multiplicativity applied in both block families. -/
theorem gamma_doubleProduct :
    ∃ G : Fin k → Fin l → RationalFunctions,
      (∀ i j, IsPadicSymmetricGammaFactor F ψ ν.val (π i) (σ j) (G i j)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val
        (F.canonicalNormalizedProductInduced (succBlockShape m hm) π)
        (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ)
        (∏ i, ∏ j, G i j) := by
  classical
  have hπind := normalizedProductWhittakerType p F ψ r k m hm π hπ
  have hσind := normalizedProductWhittakerType p F ψ t l n hn σ hσ
  obtain ⟨A, hA, houter⟩ := gammaMultiplicativity p F ψ ν t r k m hm
    (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ) π hσind hπ
  have hA' (i) := (symmetricGammaFactor_swap F ψ ν.val _ _ hσind (hπ i) (A i)).mp
    (hA i)
  have hrows : ∀ i, ∃ G : Fin l → RationalFunctions,
      (∀ j, IsPadicSymmetricGammaFactor F ψ ν.val (π i) (σ j) (G j)) ∧
      A i = ∏ j, G j := by
    intro i
    obtain ⟨G, hG, hrow⟩ := gammaMultiplicativity p F ψ ν (m i) t l n hn
      (π i) σ (hπ i) hσ
    exact ⟨G, hG, (hA' i).unique hrow⟩
  choose G hG hAG using hrows
  refine ⟨G, hG, ?_⟩
  have hout := (symmetricGammaFactor_swap F ψ ν.val _ _ hσind hπind (∏ i, A i)).mp houter
  simpa only [hAG] using hout

include hπ hσ in
/-- Certified original and actual inverse-transpose dual polynomials determine
the reflected ratio, using published gamma multiplicativity in both families. -/
theorem nonempty_reflectedRatioData
    (P PD : ℂ[X]) (Q QD : Fin k → Fin l → ℂ[X])
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      (F.canonicalNormalizedProductInduced (succBlockShape m hm) π)
      (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ) P)
    (hQ : ∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val (π i) (σ j) (Q i j))
    (hPD : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback
          (F.canonicalNormalizedProductInduced (succBlockShape m hm) π))
        (inverseTransposePullback
          (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ)) PD)
    (hQD : ∀ i j, letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback (π i)) (inverseTransposePullback (σ j)) (QD i j)) :
    Nonempty (ReflectedRatioData (LocalFactor.residueReflection F)
      P PD (∏ i, ∏ j, Q i j) (∏ i, ∏ j, QD i j)) := by
  classical
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have hπind := normalizedProductWhittakerType p F ψ r k m hm π hπ
  have hσind := normalizedProductWhittakerType p F ψ t l n hn σ hσ
  obtain ⟨e₀, he₀⟩ := epsilon_exists_of_whittakerType F ψ ν _ _ hπind hσind
  have he : ∀ i j, ∃ e : ℂˣ × ℤ,
      IsPadicSymmetricEpsilonFactor F ψ ν.val (π i) (σ j) e :=
    fun i j => epsilon_exists_of_whittakerType F ψ ν (π i) (σ j) (hπ i) (hσ j)
  choose e he using he
  obtain ⟨G, hG, hGind⟩ := gamma_doubleProduct F ψ ν m n hm hn π σ hπ hσ
  have hblock (i j) : G i j =
      rationalGammaExpression (LocalFactor.residueReflection F)
        (e i j).1 (e i j).2 (Q i j) (QD i j) :=
    (symmetricGammaExpression p F ψ ν (m i) (n j) (π i) (σ j)
      (whittakerTypeGammaConstructionInput p F ψ ν (m i) (n j)
        (V i) (W j) (π i) (σ j) (hπ i) (hσ j))
      (e i j) (Q i j) (QD i j) (he i j) (hQ i j) (hQD i j) (G i j)).mp (hG i j)
  have hind : (∏ i, ∏ j, G i j) =
      rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2 P PD :=
    (symmetricGammaExpression p F ψ ν r t _ _
      (whittakerTypeGammaConstructionInput p F ψ ν r t _ _ _ _ hπind hσind)
      e₀ P PD he₀ hP hPD (∏ i, ∏ j, G i j)).mp hGind
  have hprod :
      rationalGammaExpression (LocalFactor.residueReflection F)
        (∏ i, ∏ j, (e i j).1) (∑ i, ∑ j, (e i j).2)
        (∏ i, ∏ j, Q i j) (∏ i, ∏ j, QD i j) =
      rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2 P PD := by
    rw [rationalGammaExpression_prod]
    simp_rw [rationalGammaExpression_prod, ← hblock]
    exact hind
  exact ⟨{
    coefficient := e₀.1 / (∏ i, ∏ j, (e i j).1)
    exponent := e₀.2 - (∑ i, ∑ j, (e i j).2)
    ratio := reflectedRatio_of_gammaExpression_eq _ _ _ _ _ _ _ _ _ hprod }⟩

end Families

end TemperedLFactorGamma

end Langlands.RankinSelberg
