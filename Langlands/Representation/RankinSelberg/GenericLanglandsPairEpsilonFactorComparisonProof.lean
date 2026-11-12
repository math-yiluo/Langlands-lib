import Langlands.Correspondence.SegmentEpsilonAlgebra
import Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonStatement
import Langlands.Representation.RankinSelberg.TemperedLFactorDual
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof
import Langlands.Representation.RankinSelberg.SquareIntegrableDataLFactorProof
import Langlands.Representation.RankinSelberg.LanglandsPairEpsilonBlockExistence
import Langlands.Representation.RankinSelberg.SupercuspidalLanglandsEpsilon
import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization

/-!
# Classification and integral epsilon factors of generic pairs agree

Proof of `GenericLanglandsPairEpsilonFactorComparisonStatement`. For generic `π`
and `σ` presented by square-integrable Langlands data with standard modules `ξ`
and `η`, published gamma multiplicativity in both block families expresses the
gamma factor of `ξ × η` in two ways. The L-polynomial of `ξ × η` is the product
of the block L-polynomials, and the two dual L-polynomials have constant term
one, so the two epsilon monomials agree. The epsilon relation of `ξ × η` then
passes to the quotient pair `π × σ`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial
open PadicField.TopologicalData

universe uF uV uW uV₂ uW₂

namespace GenericEpsilonComparison

/-! ### Rational cancellation -/

/-- Two nonzero constants times integer powers of `X` times polynomials with
constant term one agree only if the constants and the exponents agree. -/
theorem monomial_mul_eq_of_coeff_zero {a a' : ℂ} (ha : a ≠ 0) (ha' : a' ≠ 0) {k k' : ℤ}
    {D D' : ℂ[X]} (hD : D.coeff 0 = 1) (hD' : D'.coeff 0 = 1)
    (h : algebraMap ℂ (RatFunc ℂ) a * (RatFunc.X : RatFunc ℂ) ^ k *
        algebraMap ℂ[X] (RatFunc ℂ) D =
      algebraMap ℂ (RatFunc ℂ) a' * (RatFunc.X : RatFunc ℂ) ^ k' *
        algebraMap ℂ[X] (RatFunc ℂ) D') :
    k = k' ∧ a = a' := by
  set N : ℕ := k.natAbs + k'.natAbs with hN
  have hk : 0 ≤ k + N := by omega
  have hk' : 0 ≤ k' + N := by omega
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hpow (j : ℤ) (hj : 0 ≤ j + N) : (RatFunc.X : RatFunc ℂ) ^ j =
      algebraMap ℂ[X] (RatFunc ℂ) (X ^ (j + N).toNat) *
        (RatFunc.X : RatFunc ℂ) ^ (-(N : ℤ)) := by
    rw [map_pow, RatFunc.algebraMap_X, ← zpow_natCast, Int.toNat_of_nonneg hj,
      ← zpow_add₀ hX]
    congr 1
    ring
  have hC (c : ℂ) : algebraMap ℂ (RatFunc ℂ) c = algebraMap ℂ[X] (RatFunc ℂ) (C c) := by
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [hpow k hk, hpow k' hk', hC, hC] at h
  have hpoly : C a * X ^ (k + N).toNat * D = C a' * X ^ (k' + N).toNat * D' := by
    apply RatFunc.algebraMap_injective ℂ
    apply mul_right_cancel₀ (zpow_ne_zero (-(N : ℤ)) hX)
    simp only [map_mul]
    calc _ = _ := by ring
      _ = _ := h
      _ = _ := by ring
  have hlow {i j : ℕ} {b b' : ℂ} {E E' : ℂ[X]} (hb : b ≠ 0) (hE : E.coeff 0 = 1)
      (hij : i < j) (heq : C b * X ^ i * E = C b' * X ^ j * E') : False := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have hcancel : C b * E = C b' * X ^ (d + 1) * E' := by
      apply mul_left_cancel₀ (pow_ne_zero i (X_ne_zero : (X : ℂ[X]) ≠ 0))
      calc X ^ i * (C b * E) = C b * X ^ i * E := by ring
        _ = C b' * X ^ (i + d + 1) * E' := heq
        _ = X ^ i * (C b' * X ^ (d + 1) * E') := by ring
    have h0 := congrArg (fun A : ℂ[X] => A.coeff 0) hcancel
    simp only [mul_coeff_zero, coeff_C_zero, hE, coeff_X_pow, mul_one] at h0
    simp only [show ¬(0 = d + 1) by omega, ↓reduceIte, mul_zero, zero_mul] at h0
    exact hb h0
  rcases lt_trichotomy (k + N).toNat (k' + N).toNat with hlt | heq | hgt
  · exact (hlow ha hD hlt hpoly).elim
  · have hcancel : C a * D = C a' * D' := by
      apply mul_left_cancel₀ (pow_ne_zero (k + N).toNat (X_ne_zero : (X : ℂ[X]) ≠ 0))
      calc X ^ (k + N).toNat * (C a * D) = C a * X ^ (k + N).toNat * D := by ring
        _ = C a' * X ^ (k' + N).toNat * D' := hpoly
        _ = X ^ (k + N).toNat * (C a' * D') := by rw [heq]; ring
    have h0 := congrArg (fun A : ℂ[X] => A.coeff 0) hcancel
    simp only [mul_coeff_zero, coeff_C_zero, hD, hD', mul_one] at h0
    refine ⟨?_, h0⟩
    have := Int.toNat_of_nonneg hk
    have := Int.toNat_of_nonneg hk'
    omega
  · exact (hlow ha' hD' hgt hpoly.symm).elim

/-! ### Block families -/

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

/-- For two families of Whittaker-type blocks whose normalized inductions have
as L-polynomial the product of the block L-polynomials, the product of the
block epsilon factors is the epsilon factor of the two inductions. -/
theorem isPadicSymmetricEpsilonFactor_normalizedProduct
    (hπ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i))
    (hσ : ∀ j, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j))
    (Q : Fin k → Fin l → ℂ[X])
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      (F.canonicalNormalizedProductInduced (succBlockShape m hm) π)
      (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ) (∏ i, ∏ j, Q i j))
    (hQ : ∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val (π i) (σ j) (Q i j))
    (b : Fin k → Fin l → ℂˣ × ℤ)
    (hb : ∀ i j, IsPadicSymmetricEpsilonFactor F ψ ν.val (π i) (σ j) (b i j)) :
    IsPadicSymmetricEpsilonFactor F ψ ν.val
      (F.canonicalNormalizedProductInduced (succBlockShape m hm) π)
      (F.canonicalNormalizedProductInduced (succBlockShape n hn) σ)
      (epsilonFactorProduct b) := by
  classical
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have hπind := normalizedProductWhittakerType p F ψ r k m hm π hπ
  have hσind := normalizedProductWhittakerType p F ψ t l n hn σ hσ
  obtain ⟨e₀, he₀⟩ :=
    TemperedLFactorGamma.epsilon_exists_of_whittakerType F ψ ν _ _ hπind hσind
  obtain ⟨D⟩ := TemperedLFactorDual.nonempty_dualTwoFamilyLPolynomialData
    F ψ ν m n hm hn π σ hπ hσ
  obtain ⟨G, hG, hGind⟩ :=
    TemperedLFactorGamma.gamma_doubleProduct F ψ ν m n hm hn π σ hπ hσ
  have hblock (i j) : G i j =
      rationalGammaExpression (LocalFactor.residueReflection F)
        (b i j).1 (b i j).2 (Q i j) (D.blockPolynomial i j) :=
    (symmetricGammaExpression p F ψ ν (m i) (n j) (π i) (σ j)
      (whittakerTypeGammaConstructionInput p F ψ ν (m i) (n j)
        (V i) (W j) (π i) (σ j) (hπ i) (hσ j))
      (b i j) (Q i j) (D.blockPolynomial i j) (hb i j) (hQ i j)
      (D.block_spec i j) (G i j)).mp (hG i j)
  have hind : (∏ i, ∏ j, G i j) =
      rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2
        (∏ i, ∏ j, Q i j) D.inducedPolynomial :=
    (symmetricGammaExpression p F ψ ν r t _ _
      (whittakerTypeGammaConstructionInput p F ψ ν r t _ _ _ _ hπind hσind)
      e₀ _ D.inducedPolynomial he₀ hP D.induced_spec (∏ i, ∏ j, G i j)).mp hGind
  have hprod :
      rationalGammaExpression (LocalFactor.residueReflection F)
        (epsilonFactorProduct b).1 (epsilonFactorProduct b).2
        (∏ i, ∏ j, Q i j) (∏ i, ∏ j, D.blockPolynomial i j) =
      rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2
        (∏ i, ∏ j, Q i j) D.inducedPolynomial := by
    change rationalGammaExpression _ (∏ i, ∏ j, (b i j).1) (∑ i, ∑ j, (b i j).2) _ _ = _
    rw [TemperedLFactorGamma.rationalGammaExpression_prod]
    simp_rw [TemperedLFactorGamma.rationalGammaExpression_prod, ← hblock]
    exact hind
  have hP0 : (∏ i, ∏ j, Q i j) ≠ 0 := fun h0 => by
    have := hP.coeff_zero
    rw [h0, coeff_zero] at this
    exact zero_ne_one this
  have hD : (∏ i, ∏ j, D.blockPolynomial i j).coeff 0 = 1 := by
    simp only [coeff_zero_prod, fun i j => (D.block_spec i j).coeff_zero,
      Finset.prod_const_one]
  obtain ⟨hc, hexp⟩ :=
    rationalGammaExpression_cancel hP0 hD D.induced_spec.coeff_zero hprod
  have he : epsilonFactorProduct b = e₀ := Prod.ext hc hexp
  rw [he]
  exact he₀

end Families

/-! ### Surjective pullback of the epsilon relation -/

section Surjective

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {e : ℂˣ × ℤ}

/-- The equal-rank epsilon relation passes to quotients along surjective
intertwiners, provided the quotients carry nonzero functionals. -/
theorem isEqualRankEpsilonFactor_of_surjective
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (g : σ.IntertwiningMap σ₂) (hg : Function.Surjective g)
    (hℓ : ∃ ℓ : glFunctionals ψ n π₂, ℓ.val ≠ 0)
    (hℓ' : ∃ ℓ' : glInverseFunctionals ψ n σ₂, ℓ'.val ≠ 0)
    (h : IsEqualRankEpsilonFactor q ψ abv ν π σ e) :
    IsEqualRankEpsilonFactor q ψ abv ν π₂ σ₂ e := by
  obtain ⟨hμ, -, -, hall⟩ := h
  refine ⟨hμ, hℓ, hℓ', ?_⟩
  intro hinv μ hμc ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  exact (EqualRankEpsilonEquation.congr_model (coefficientModel_functionalsComap f hf ℓ₂)
    (coefficientModel_functionalsComap g hg ℓ₂')).mp
    (@hall hinv μ hμc _ _ (functionalsComap_ne_zero f hf ℓ₂ hℓ₂)
      (functionalsComap_ne_zero g hg ℓ₂' hℓ₂'))

/-- The unequal-rank analogue of `isEqualRankEpsilonFactor_of_surjective`. -/
theorem isUnequalRankEpsilonFactor_of_surjective {hnr : n < r}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (g : σ.IntertwiningMap σ₂) (hg : Function.Surjective g)
    (hℓ : ∃ ℓ : glFunctionals ψ r π₂, ℓ.val ≠ 0)
    (hℓ' : ∃ ℓ' : glInverseFunctionals ψ n σ₂, ℓ'.val ≠ 0)
    (h : IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e) :
    IsUnequalRankEpsilonFactor hnr q ψ abv ν π₂ σ₂ e := by
  obtain ⟨hμ, -, -, hall⟩ := h
  refine ⟨hμ, hℓ, hℓ', ?_⟩
  intro hinv μ hμc ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  exact (UnequalRankEpsilonEquation.congr_model (coefficientModel_functionalsComap f hf ℓ₂)
    (coefficientModel_functionalsComap g hg ℓ₂')).mp
    (@hall hinv μ hμc _ _ (functionalsComap_ne_zero f hf ℓ₂ hℓ₂)
      (functionalsComap_ne_zero g hg ℓ₂' hℓ₂'))

/-- The pair epsilon relation passes to quotients along surjective intertwiners. -/
theorem isPairEpsilonFactor_of_surjective
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (g : σ.IntertwiningMap σ₂) (hg : Function.Surjective g)
    (hℓ : ∃ ℓ : glFunctionals ψ r π₂, ℓ.val ≠ 0)
    (hℓ' : ∃ ℓ' : glInverseFunctionals ψ n σ₂, ℓ'.val ≠ 0)
    (h : IsPairEpsilonFactor q ψ abv ν π σ e) : IsPairEpsilonFactor q ψ abv ν π₂ σ₂ e := by
  by_cases hnr : n < r
  · rw [isPairEpsilonFactor_of_lt hnr] at h ⊢
    exact isUnequalRankEpsilonFactor_of_surjective f hf g hg hℓ hℓ' h
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairEpsilonFactor_self] at h ⊢
      exact isEqualRankEpsilonFactor_of_surjective f hf g hg hℓ hℓ' h
    · exact absurd h (not_isPairEpsilonFactor_of_lt (by omega))

end Surjective

section PadicSurjective

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {e : ℂˣ × ℤ}

/-- The p-adic pair epsilon relation passes to quotients along surjective
intertwiners, provided the quotients carry nonzero functionals. -/
theorem isPadicPairEpsilonFactor_of_surjective
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (g : σ.IntertwiningMap σ₂) (hg : Function.Surjective g)
    (hℓ : letI := F.canonicalTopologicalData.topology
      ∃ ℓ : glFunctionals ψ r π₂, ℓ.val ≠ 0)
    (hℓ' : letI := F.canonicalTopologicalData.topology
      ∃ ℓ' : glInverseFunctionals ψ n σ₂, ℓ'.val ≠ 0)
    (h : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    IsPadicPairEpsilonFactor F ψ ν π₂ σ₂ e := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact isPairEpsilonFactor_of_surjective f hf g hg hℓ hℓ' h

/-- The symmetric p-adic epsilon relation passes to quotients along surjective
intertwiners, provided both quotients carry nonzero functionals for the
standard and the inverse character. -/
theorem isPadicSymmetricEpsilonFactor_of_surjective
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
    {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (g : σ.IntertwiningMap σ₂) (hg : Function.Surjective g)
    (hπ₂ : letI := F.canonicalTopologicalData.topology
      ∃ ℓ : glFunctionals ψ r π₂, ℓ.val ≠ 0)
    (hπ₂' : letI := F.canonicalTopologicalData.topology
      ∃ ℓ : glInverseFunctionals ψ r π₂, ℓ.val ≠ 0)
    (hσ₂ : letI := F.canonicalTopologicalData.topology
      ∃ ℓ : glFunctionals ψ n σ₂, ℓ.val ≠ 0)
    (hσ₂' : letI := F.canonicalTopologicalData.topology
      ∃ ℓ : glInverseFunctionals ψ n σ₂, ℓ.val ≠ 0)
    (h : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    IsPadicSymmetricEpsilonFactor F ψ ν π₂ σ₂ e := by
  unfold IsPadicSymmetricEpsilonFactor at h ⊢
  split_ifs at h ⊢
  · exact isPadicPairEpsilonFactor_of_surjective f hf g hg hπ₂ hσ₂' h
  · exact isPadicPairEpsilonFactor_of_surjective g hg f hf hσ₂ hπ₂' h

end PadicSurjective

/-! ### Square-integrable blocks -/

section Blocks

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)

/-- An irreducible essentially square-integrable block of positive rank has a
nonzero Whittaker functional, in every carrier universe. -/
theorem hasFunctional_of_essentiallySquareIntegrable {k : ℕ} (hk : 0 < k)
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear k F.Carrier))
    (hirr : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible A.representation)
    (hA : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable A.representation) :
    letI := F.canonicalTopologicalData.topology
    HasFunctional (N := upperUnipotent k F.Carrier)
      (θ := entrywiseCharacter ψ.complex k) A.representation := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  let E := SmoothRep.universeLiftEquiv.{uF} A
  have hgen := essentiallySquareIntegrable_isGeneric.{uF, uV} F F.canonicalTopologicalData n
    (SmoothRep.universeLift.{uF} A) ((isIrreducible_iff_of_equiv E).mp hirr)
    ((F.canonicalTopologicalData.isEssentiallySquareIntegrable_iff_of_equiv E).mp hA) ψ
  obtain ⟨ℓ, hℓ⟩ := hgen.2.2
  rw [entrywiseCharacter_eq_standardCharacter]
  exact ⟨functionalPullback E ℓ, functionalPullback_ne_zero E hℓ⟩

variable (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- `isPadicSymmetricEpsilonFactor_normalizedProduct` for arbitrary block
shapes: blocks that are irreducible, admissible and carry nonzero Whittaker
functionals. -/
theorem isPadicSymmetricEpsilonFactor_normalizedProduct_of_blocks {r t : ℕ}
    (B : BlockShape (r + 1)) (C : BlockShape (t + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin C.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (B.size i) F.Carrier) (V i))
    (σ : ∀ j, Representation ℂ (Langlands.GeneralLinear (C.size j) F.Carrier) (W j))
    (hπirr : ∀ i, Representation.IsIrreducible (π i))
    (hπadm : ∀ i, letI := F.canonicalTopologicalData.topology; IsAdmissible (π i))
    (hπfun : ∀ i, letI := F.canonicalTopologicalData.topology
      HasFunctional (N := upperUnipotent (B.size i) F.Carrier)
        (θ := entrywiseCharacter ψ.complex (B.size i)) (π i))
    (hσirr : ∀ j, Representation.IsIrreducible (σ j))
    (hσadm : ∀ j, letI := F.canonicalTopologicalData.topology; IsAdmissible (σ j))
    (hσfun : ∀ j, letI := F.canonicalTopologicalData.topology
      HasFunctional (N := upperUnipotent (C.size j) F.Carrier)
        (θ := entrywiseCharacter ψ.complex (C.size j)) (σ j))
    (Q : Fin B.length → Fin C.length → ℂ[X])
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      (F.canonicalNormalizedProductInduced B π) (F.canonicalNormalizedProductInduced C σ)
      (∏ i, ∏ j, Q i j))
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ ν.val (π i) (σ j) (Q i j))
    (b : Fin B.length → Fin C.length → ℂˣ × ℤ)
    (hb : ∀ i j, IsPadicRankEpsilonFactor F ψ ν.val (π i) (σ j) (b i j)) :
    IsPadicSymmetricEpsilonFactor F ψ ν.val
      (F.canonicalNormalizedProductInduced B π) (F.canonicalNormalizedProductInduced C σ)
      (epsilonFactorProduct b) := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨k, size, pos, total⟩ := B
  obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => by
      have := pos i
      show size i = size i - 1 + 1
      omega⟩
  obtain ⟨l, size', pos', total'⟩ := C
  obtain ⟨n, rfl⟩ : ∃ n : Fin l → ℕ, size' = fun j => n j + 1 :=
    ⟨fun j => size' j - 1, funext fun j => by
      have := pos' j
      show size' j = size' j - 1 + 1
      omega⟩
  have hπwt (i) : IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i) := by
    have h : HasFunctional (N := upperUnipotent (m i + 1) F.Carrier)
        (θ := entrywiseCharacter ψ.complex (m i + 1)) (π i) := hπfun i
    rw [entrywiseCharacter_eq_standardCharacter] at h
    exact isOfWhittakerType_of_isGeneric F ⟨hπirr i, hπadm i, h⟩
  have hσwt (j) : IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j) := by
    have h : HasFunctional (N := upperUnipotent (n j + 1) F.Carrier)
        (θ := entrywiseCharacter ψ.complex (n j + 1)) (σ j) := hσfun j
    rw [entrywiseCharacter_eq_standardCharacter] at h
    exact isOfWhittakerType_of_isGeneric F ⟨hσirr j, hσadm j, h⟩
  exact isPadicSymmetricEpsilonFactor_normalizedProduct F ψ ν m n total total' π σ
    hπwt hσwt Q hP hQ b hb

end Blocks

end GenericEpsilonComparison

/-- Henniart 2002, 2.8, for generic pairs: the epsilon factor of `(π, σ)`
through square-integrable Langlands data is the JPSS epsilon factor of the
pair itself. -/
theorem genericLanglandsPairEpsilonFactorComparison :
    GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t π σ hπ hσ e he
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩, hall⟩ := he
  obtain ⟨b, hb, rfl⟩ := hall d d' hd hd'
  obtain ⟨P, Q, hPL, hQ, hPQ⟩ :=
    squareIntegrableDataLFactor.{uF, uV, uW} p F ψ ν r t d d' π σ hd hd'
  obtain ⟨⟨dt, hdt⟩, ⟨et, het⟩, hstd⟩ := hPL
  obtain ⟨P', hP'std, hP'⟩ :=
    genericLanglandsQuotientLFactor.{uF, uV, uW} p F ψ ν r t dt et π σ hdt het hπ hσ
  obtain rfl : P' = P := hP'std.unique (hstd dt et hdt het)
  obtain ⟨-, f, hf⟩ := hd
  obtain ⟨-, g, hg⟩ := hd'
  have hξ : IsOfWhittakerType r (standardCharacter ψ r)
      (F.canonicalNormalizedProductInduced d.shape fun i => (d.blocks i).representation) :=
    normalizedProduct_isOfWhittakerType_of_blocks F ψ r d.shape _ d.irreducible
      (fun i => (d.essentiallySquareIntegrable i).isAdmissible)
      (fun i => GenericEpsilonComparison.hasFunctional_of_essentiallySquareIntegrable F ψ
        (d.shape.positive i) (d.blocks i) (d.irreducible i) (d.essentiallySquareIntegrable i))
  have hη : IsOfWhittakerType t (standardCharacter ψ t)
      (F.canonicalNormalizedProductInduced d'.shape fun j => (d'.blocks j).representation) :=
    normalizedProduct_isOfWhittakerType_of_blocks F ψ t d'.shape _ d'.irreducible
      (fun j => (d'.essentiallySquareIntegrable j).isAdmissible)
      (fun j => GenericEpsilonComparison.hasFunctional_of_essentiallySquareIntegrable F ψ
        (d'.shape.positive j) (d'.blocks j) (d'.irreducible j)
        (d'.essentiallySquareIntegrable j))
  have hπ' := (isOfInverseWhittakerType_of_isGeneric F hπ).exists_ne_zero
  have hσ' := (isOfInverseWhittakerType_of_isGeneric F hσ).exists_ne_zero
  have hPind : IsPadicSymmetricLPolynomial F ψ ν.val
      (F.canonicalNormalizedProductInduced d.shape fun i => (d.blocks i).representation)
      (F.canonicalNormalizedProductInduced d'.shape fun j => (d'.blocks j).representation)
      (∏ i, ∏ j, Q i j) := by
    rw [← hPQ]
    refine (isPadicSymmetricLPolynomial_congr_whittakerSets ?_ ?_ ?_ ?_).mpr hP'
    · exact whittakerSet_eq_of_surjective_of_whittakerType ψ hξ f hf hπ.2.2
    · exact inverseWhittakerSet_eq_of_surjective_of_whittakerType ψ
        ((isOfWhittakerType_standard_iff_inverse ψ _).mp hξ) f hf hπ'
    · exact whittakerSet_eq_of_surjective_of_whittakerType ψ hη g hg hσ.2.2
    · exact inverseWhittakerSet_eq_of_surjective_of_whittakerType ψ
        ((isOfWhittakerType_standard_iff_inverse ψ _).mp hη) g hg hσ'
  have hε := GenericEpsilonComparison.isPadicSymmetricEpsilonFactor_normalizedProduct_of_blocks
    F ψ ν d.shape d'.shape _ _ d.irreducible
    (fun i => (d.essentiallySquareIntegrable i).isAdmissible)
    (fun i => GenericEpsilonComparison.hasFunctional_of_essentiallySquareIntegrable F ψ
      (d.shape.positive i) (d.blocks i) (d.irreducible i) (d.essentiallySquareIntegrable i))
    d'.irreducible (fun j => (d'.essentiallySquareIntegrable j).isAdmissible)
    (fun j => GenericEpsilonComparison.hasFunctional_of_essentiallySquareIntegrable F ψ
      (d'.shape.positive j) (d'.blocks j) (d'.irreducible j)
      (d'.essentiallySquareIntegrable j))
    Q hPind hQ b hb
  exact GenericEpsilonComparison.isPadicSymmetricEpsilonFactor_of_surjective f hf g hg
    hπ.2.2 hπ' hσ.2.2 hσ' hε

end Langlands.RankinSelberg
