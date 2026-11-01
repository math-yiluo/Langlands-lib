import Langlands.Representation.RankinSelberg.AdjacentRankLaurentSpecialization
import Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof
import Langlands.Representation.Shahidi.Induction

/-! Actual unramified polynomial kernels with entire coefficients and fixed finite support. -/

noncomputable section

namespace Langlands.RankinSelberg.ParameterSpecialization

open HarmonicAnalysis Polynomial
open scoped BigOperators

/-- The kernel hypotheses needed for actual bilateral Laurent specialization. -/
def EntireUniformLaurentKernel (P : ℂ → LaurentPolynomial ℂ) : Prop :=
  ∃ S : Finset ℤ, (∀ u, (P u).coeff.support ⊆ S) ∧
    ∀ j u, AnalyticAt ℂ (fun z => (P z).coeff j) u

/-- The product of the fixed equal-rank polynomial and the actual unramified
rescaling of the rank-one polynomial, embedded into Laurent polynomials. -/
def spectralClearingKernel (q : ℕ) (P₀ P₁ : Polynomial ℂ) (u : ℂ) :
    LaurentPolynomial ℂ :=
  (P₀ * P₁.comp (C (spectralPoint q u) * X)).toLaurent

@[simp]
theorem spectralClearingKernel_zero (q : ℕ) (P₀ P₁ : Polynomial ℂ) :
    spectralClearingKernel q P₀ P₁ 0 = (P₀ * P₁).toLaurent := by
  simp [spectralClearingKernel, spectralPoint]

private theorem toLaurent_coeff_nat (P : Polynomial ℂ) (n : ℕ) :
    P.toLaurent.coeff (n : ℤ) = P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

private theorem toLaurent_coeff_negSucc (P : Polynomial ℂ) (n : ℕ) :
    P.toLaurent.coeff (Int.negSucc n) = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, hk⟩
  change (k : ℤ) = Int.negSucc n at hk
  omega

/-- The exact L-denominator rescaling has entire coefficients and a common
finite exponent set, independently of the complex parameter. -/
theorem spectralClearingKernel_entire_uniform
    {q : ℕ} (hq : 1 < q) (P₀ P₁ : Polynomial ℂ) :
    EntireUniformLaurentKernel (spectralClearingKernel q P₀ P₁) := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hpoint : Differentiable ℂ (spectralPoint q) := by
    exact (TwoBlockDeformation.differentiable_ofReal_cpow hqpos).comp
      differentiable_id.neg
  have hrescale : ∀ n : ℕ, Differentiable ℂ (fun u =>
      (P₁.comp (C (spectralPoint q u) * X)).coeff n) := by
    intro n
    simp only [Polynomial.comp_C_mul_X_coeff]
    exact (hpoint.pow n).const_mul (P₁.coeff n)
  have hproduct : ∀ n : ℕ, Differentiable ℂ (fun u =>
      (P₀ * P₁.comp (C (spectralPoint q u) * X)).coeff n) := by
    intro n
    simp only [Polynomial.coeff_mul]
    exact Differentiable.fun_sum fun j _ => (hrescale j.2).const_mul (P₀.coeff j.1)
  refine ⟨(Finset.range (P₀.natDegree + P₁.natDegree + 1)).map Nat.castEmbedding, ?_, ?_⟩
  · intro u m hm
    rw [spectralClearingKernel, LaurentPolynomial.support_coeff_toLaurent] at hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hm
    refine Finset.mem_map.mpr ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    have hsmall : (C (spectralPoint q u) * X : Polynomial ℂ).natDegree ≤ 1 := by
      simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] using
        (Polynomial.natDegree_mul_le (p := C (spectralPoint q u)) (q := X))
    have hdegree : (P₁.comp (C (spectralPoint q u) * X)).natDegree ≤ P₁.natDegree := by
      calc
        _ ≤ P₁.natDegree * (C (spectralPoint q u) * X : Polynomial ℂ).natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ P₁.natDegree * 1 := Nat.mul_le_mul_left _ hsmall
        _ = P₁.natDegree := mul_one _
    have hnle := Polynomial.le_natDegree_of_mem_supp _ hn
    have hprod := Polynomial.natDegree_mul_le
      (p := P₀) (q := P₁.comp (C (spectralPoint q u) * X))
    omega
  · intro j u
    cases j with
    | ofNat n =>
      change AnalyticAt ℂ (fun z => (spectralClearingKernel q P₀ P₁ z).coeff (n : ℤ)) u
      simpa only [spectralClearingKernel, toLaurent_coeff_nat] using (hproduct n).analyticAt u
    | negSucc n =>
      simp only [spectralClearingKernel, toLaurent_coeff_negSucc]
      exact analyticAt_const

/-- For the actual rescaled product kernel all kernel-analyticity and support
premises of Laurent specialization are discharged. Slice analyticity and
formal clearing on the real ray remain the two substantive inputs. -/
theorem spectralKernel_laurent_clearing_of_real_gt
    {q : ℕ} (hq : 1 < q) (P₀ P₁ : Polynomial ℂ)
    (c : ℂ → BilateralLaurentSeries) (hc : EntireCoefficientFamily c)
    (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R =
        spectralClearingKernel q P₀ P₁ (u : ℂ) • c (u : ℂ)) :
    ∃ Q : ℂ → LaurentPolynomial ℂ,
      (∀ u, BilateralLaurentSeries.ofLaurentPolynomial (Q u) =
        spectralClearingKernel q P₀ P₁ u • c u) ∧
      (∃ T : Finset ℤ, ∀ u, (Q u).coeff.support ⊆ T) ∧
      EntireCoefficientFamily (fun u j => (Q u).coeff j) := by
  obtain ⟨S, hS, hA⟩ := spectralClearingKernel_entire_uniform hq P₀ P₁
  exact laurent_clearing_of_real_gt S (spectralClearingKernel q P₀ P₁) c
    hS (fun j _ => hA j) hc C hreal

/-- In particular the original product polynomial clears the actual series
at parameter zero, once the entire family and real-ray clearing are supplied. -/
theorem spectralKernel_laurent_clearing_at_zero
    {q : ℕ} (hq : 1 < q) (P₀ P₁ : Polynomial ℂ)
    (c : ℂ → BilateralLaurentSeries) (hc : EntireCoefficientFamily c)
    (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R =
        spectralClearingKernel q P₀ P₁ (u : ℂ) • c (u : ℂ)) :
    ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R = (P₀ * P₁).toLaurent • c 0 := by
  obtain ⟨Q, hQ, -, -⟩ := spectralKernel_laurent_clearing_of_real_gt hq P₀ P₁ c hc C hreal
  exact ⟨Q 0, by simpa only [spectralClearingKernel_zero] using hQ 0⟩

end Langlands.RankinSelberg.ParameterSpecialization

namespace Langlands.RankinSelberg.Padic

open HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance clearingKernelTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The published complete unramified L transport applies to the literal
complex determinant-power block family, with no transport premise. -/
theorem symmetricLPolynomial_determinantComplexPower
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W)
    (u : ℂ) (P : Polynomial ℂ)
    (hP : IsPadicSymmetricLPolynomial F ψ μ.val π σ P) :
    IsPadicSymmetricLPolynomial F ψ μ.val π
      (Langlands.twist (F.canonicalTopologicalData.determinantComplexPower (n + 1) u) σ)
      (P.comp (C (spectralPoint F.canonicalTopologicalData.residueCardinality u) * X)) := by
  let T := F.canonicalTopologicalData
  let χ := T.unramifiedCharacter
    (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos u)
  have hχ : ∀ x : F.Carrierˣ,
      (χ x : ℂ) = (T.normalizedAbs (x : F.Carrier) : ℂ) ^ u := by
    intro x
    simpa only [T.determinantNorm_scalar, pow_one, T.normalizedAbsUnits_coe,
      PadicField.TopologicalData.determinantComplexPower,
      PadicField.TopologicalData.determinantUnramifiedCharacter, MonoidHom.comp_apply,
      GeneralLinear.determinant, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using
      T.determinantComplexPower_apply 1 u (GeneralLinear.scalar x)
  exact (unramifiedTwistLFactor p F ψ μ r n π σ u χ hχ P hP).1

end Langlands.RankinSelberg.Padic
