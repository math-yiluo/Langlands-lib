import Langlands.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.AllField.Representation.RankinSelberg.TemperedLFactorDivisibility
import Langlands.AllField.Representation.RankinSelberg.GammaMultiplicativityProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.AllField.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankSwapFactors

/-!
# Gamma assembly for two block families of Whittaker type

Over a nonarchimedean local field: the canonical expression of a symmetric gamma
certificate by epsilon data and the original and dual L-polynomials; the epsilon data
of pairs of Whittaker type; gamma multiplicativity (JPSS 1983, Theorem (3.1)(i),
printed page 404) in both families; and the resulting reflected ratio identity
between the original and the inverse-transpose dual L-polynomials.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding isPadicSymmetricEpsilonFactor_of_lt EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

/-- In the smaller-rank-first order the symmetric epsilon relation is the pair
relation of the exchanged pair. -/
theorem isPadicSymmetricEpsilonFactor_of_lt
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F} {ν : letI := borel F; AdditiveHaarMeasure F}
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    (h : r < n) {e : ℂˣ × ℤ} :
    IsPadicSymmetricEpsilonFactor F ψ ν π σ e ↔ IsPadicPairEpsilonFactor F ψ ν σ π e := by
  simp only [IsPadicSymmetricEpsilonFactor, Nat.not_le.mpr h, ↓reduceIte]

/-- Every symmetric gamma certificate is exactly the canonical expression of any
supplied epsilon and original/dual polynomial certificates, under the construction
input of the pair. -/
theorem symmetricGammaExpression
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (h : PadicSymmetricGammaConstructionInput F ψ ν.val π σ)
    (e : ℂˣ × ℤ) (P Pdual : ℂ[X])
    (he : IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e)
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P)
    (hPd : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback σ) Pdual)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ ν.val π σ G ↔
      G = rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F)
        e.1 e.2 P Pdual := by
  have hG : IsPadicSymmetricGammaFactor F ψ ν.val π σ
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F)
        e.1 e.2 P Pdual) := by
    by_cases hnr : n ≤ r
    · apply (isPadicSymmetricGammaFactor_of_le hnr).mpr
      apply IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val π σ
      · unfold PadicSymmetricGammaConstructionInput at h
        rwa [ite_eq_left hnr] at h
      · exact (isPadicSymmetricEpsilonFactor_of_le hnr).mp he
      · exact (isPadicSymmetricLPolynomial_of_le hnr).mp hP
      · exact (isPadicSymmetricLPolynomial_of_le hnr).mp hPd
    · have hlt : r < n := Nat.lt_of_not_ge hnr
      apply (isPadicSymmetricGammaFactor_of_lt hlt).mpr
      apply IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val σ π
      · unfold PadicSymmetricGammaConstructionInput at h
        rwa [ite_eq_right hnr] at h
      · exact (isPadicSymmetricEpsilonFactor_of_lt hlt).mp he
      · exact (isPadicSymmetricLPolynomial_of_lt hlt).mp hP
      · exact (isPadicSymmetricLPolynomial_of_lt hlt).mp hPd
  constructor
  · intro hG'
    exact hG'.unique hG
  · intro hEq
    simpa only [hEq] using hG

namespace TemperedLFactorGamma

/-- Extract the certified epsilon data present in the Whittaker-type construction
input, in either rank order. -/
theorem epsilon_exists_of_whittakerType
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ e : ℂˣ × ℤ, IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e := by
  have h := whittakerTypeGammaConstructionInput F ψ ν r n V W π σ hπ hσ
  by_cases hnr : n ≤ r
  · have ho : PadicPairGammaConstructionInput F ψ ν.val π σ := by
      unfold PadicSymmetricGammaConstructionInput at h
      rwa [ite_eq_left hnr] at h
    obtain ⟨e, he⟩ := ho.2.2.1
    exact ⟨e, (isPadicSymmetricEpsilonFactor_of_le hnr).mpr he⟩
  · have ho : PadicPairGammaConstructionInput F ψ ν.val σ π := by
      unfold PadicSymmetricGammaConstructionInput at h
      rwa [ite_eq_right hnr] at h
    obtain ⟨e, he⟩ := ho.2.2.1
    exact ⟨e, (isPadicSymmetricEpsilonFactor_of_lt (Nat.lt_of_not_ge hnr)).mpr he⟩

/-- Fixed-character symmetric gamma exchange for representations of Whittaker type. -/
theorem symmetricGammaFactor_swap
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F) (ν : letI := borel F; AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
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
  (hπ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
  (hσ : ∀ j, IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j))

include hπ hσ in
/-- Gamma multiplicativity applied in both block families. -/
theorem gamma_doubleProduct :
    ∃ G : Fin k → Fin l → RationalFunctions,
      (∀ i j, IsPadicSymmetricGammaFactor F ψ ν.val (π i) (σ j) (G i j)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m hm) π)
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape n hn) σ)
        (∏ i, ∏ j, G i j) := by
  classical
  have hπind := normalizedProductWhittakerType F ψ r k m hm π hπ
  have hσind := normalizedProductWhittakerType F ψ t l n hn σ hσ
  obtain ⟨A, hA, houter⟩ := gammaMultiplicativity F ψ ν t r k m hm
    ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape n hn) σ) π hσind hπ
  have hA' (i) := (symmetricGammaFactor_swap F ψ ν.val _ _ hσind (hπ i) (A i)).mp
    (hA i)
  have hrows : ∀ i, ∃ G : Fin l → RationalFunctions,
      (∀ j, IsPadicSymmetricGammaFactor F ψ ν.val (π i) (σ j) (G j)) ∧
      A i = ∏ j, G j := by
    intro i
    obtain ⟨G, hG, hrow⟩ := gammaMultiplicativity F ψ ν (m i) t l n hn
      (π i) σ (hπ i) hσ
    exact ⟨G, hG, (hA' i).unique hrow⟩
  choose G hG hAG using hrows
  refine ⟨G, hG, ?_⟩
  have hout := (symmetricGammaFactor_swap F ψ ν.val _ _ hσind hπind (∏ i, A i)).mp houter
  simpa only [hAG] using hout

include hπ hσ in
/-- Certified original and inverse-transpose dual polynomials determine the
reflected ratio, by gamma multiplicativity in both families. -/
theorem nonempty_reflectedRatioData
    (P PD : ℂ[X]) (Q QD : Fin k → Fin l → ℂ[X])
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m hm) π)
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape n hn) σ) P)
    (hQ : ∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val (π i) (σ j) (Q i j))
    (hPD : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m hm) π))
        (inverseTransposePullback
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape n hn) σ)) PD)
    (hQD : ∀ i j, IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback (π i)) (inverseTransposePullback (σ j)) (QD i j)) :
    Nonempty (Langlands.RankinSelberg.TemperedLFactorGamma.ReflectedRatioData
      (Langlands.AllField.LocalFactor.residueReflection F)
      P PD (∏ i, ∏ j, Q i j) (∏ i, ∏ j, QD i j)) := by
  classical
  have hπind := normalizedProductWhittakerType F ψ r k m hm π hπ
  have hσind := normalizedProductWhittakerType F ψ t l n hn σ hσ
  obtain ⟨e₀, he₀⟩ := epsilon_exists_of_whittakerType F ψ ν _ _ hπind hσind
  have he : ∀ i j, ∃ e : ℂˣ × ℤ,
      IsPadicSymmetricEpsilonFactor F ψ ν.val (π i) (σ j) e :=
    fun i j => epsilon_exists_of_whittakerType F ψ ν (π i) (σ j) (hπ i) (hσ j)
  choose e he using he
  obtain ⟨G, hG, hGind⟩ := gamma_doubleProduct F ψ ν m n hm hn π σ hπ hσ
  have hblock (i j) : G i j =
      rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F)
        (e i j).1 (e i j).2 (Q i j) (QD i j) :=
    (symmetricGammaExpression F ψ ν (m i) (n j) (π i) (σ j)
      (whittakerTypeGammaConstructionInput F ψ ν (m i) (n j)
        (V i) (W j) (π i) (σ j) (hπ i) (hσ j))
      (e i j) (Q i j) (QD i j) (he i j) (hQ i j) (hQD i j) (G i j)).mp (hG i j)
  have hind : (∏ i, ∏ j, G i j) =
      rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F)
        e₀.1 e₀.2 P PD :=
    (symmetricGammaExpression F ψ ν r t _ _
      (whittakerTypeGammaConstructionInput F ψ ν r t _ _ _ _ hπind hσind)
      e₀ P PD he₀ hP hPD (∏ i, ∏ j, G i j)).mp hGind
  have hprod :
      rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F)
        (∏ i, ∏ j, (e i j).1) (∑ i, ∑ j, (e i j).2)
        (∏ i, ∏ j, Q i j) (∏ i, ∏ j, QD i j) =
      rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F)
        e₀.1 e₀.2 P PD := by
    rw [Langlands.RankinSelberg.TemperedLFactorGamma.rationalGammaExpression_prod]
    simp_rw [Langlands.RankinSelberg.TemperedLFactorGamma.rationalGammaExpression_prod,
      ← hblock]
    exact hind
  exact ⟨{
    coefficient := e₀.1 / (∏ i, ∏ j, (e i j).1)
    exponent := e₀.2 - (∑ i, ∑ j, (e i j).2)
    ratio := Langlands.RankinSelberg.TemperedLFactorGamma.reflectedRatio_of_gammaExpression_eq
      _ _ _ _ _ _ _ _ _ hprod }⟩

end Families

end TemperedLFactorGamma

end Langlands.AllField.RankinSelberg
