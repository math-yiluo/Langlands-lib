import Langlands.Representation.Conductor.EssentialRestrictionUniqueness
import Langlands.Representation.Conductor.SphericalRational

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Filter Topology Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- Finite multiplication of a convergent bilateral Laurent series. -/
theorem hasSum_laurent_mul_polynomial {c : ℤ → ℂ} {z v : ℂ} (hz : z ≠ 0)
    (hc : HasSum (fun d : ℤ => c d * z ^ d) v) (P : Polynomial ℂ) :
    HasSum (fun d : ℤ => (∑ m ∈ P.support, c (d - (m : ℤ)) * P.coeff m) * z ^ d)
      (v * P.eval z) := by
  classical
  have hm (m : ℕ) :
      HasSum (fun d : ℤ => c (d - (m : ℤ)) * P.coeff m * z ^ d)
        (v * (P.coeff m * z ^ m)) := by
    have ht := ((Equiv.subRight (m : ℤ)).hasSum_iff).mpr hc
    have ht' := ht.mul_right (P.coeff m * z ^ m)
    convert ht' using 1
    funext d
    change c (d - (m : ℤ)) * P.coeff m * z ^ d =
      c (d - (m : ℤ)) * z ^ (d - (m : ℤ)) * (P.coeff m * z ^ m)
    rw [← zpow_natCast]
    calc
      _ = c (d - (m : ℤ)) * P.coeff m *
          (z ^ (d - (m : ℤ)) * z ^ (m : ℤ)) := by
        rw [← zpow_add₀ hz, sub_add_cancel]
      _ = _ := by ring
  have hs := hasSum_sum (s := P.support) (fun m _ => hm m)
  convert hs using 1
  · funext d
    rw [Finset.sum_mul]
  · rw [← Finset.mul_sum, Polynomial.eval_eq_sum]
    rfl

/-- Coefficientwise evaluation commutes with the convergent finite convolution. -/
theorem hasSum_mapped_laurent_mul_polynomial {A : Type*} [CommRing A]
    (f : A →+* ℂ) (S : LaurentSeries A) {z v : ℂ} (hz : z ≠ 0)
    (hc : HasSum (fun d : ℤ => f (S.coeff d) * z ^ d) v) (P : Polynomial A) :
    HasSum (fun d : ℤ => f ((S * finitePolynomialLaurentSeries P).coeff d) * z ^ d)
      (v * (P.map f).eval z) := by
  have hm := hasSum_laurent_mul_polynomial hz hc (P.map f)
  convert hm using 1
  funext d
  change ((S * finitePolynomialLaurentSeries P).map f).coeff d * z ^ d = _
  rw [mul_finitePolynomialLaurentSeries_map, mul_finitePolynomialLaurentSeries_coeff]
  rfl

/-- The subalgebra of symmetric Laurent polynomials that are actual polynomials. -/
def symmetricPolynomialTorusSubalgebra
    (σ : Type*) (K : Type*) [Fintype σ] [Field K] :
    Subalgebra K (symmetricTorusSubalgebra σ K) :=
  (symmetricPolynomialToTorus σ K).range

/-- Multiplication of the essential factor by its polynomial denominator is one
also at every point where the essential factor is regular. -/
theorem essentialFactor_eval_mul_denominator {m : ℕ} (P : Polynomial ℂ)
    (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) (z : ℂ)
    (hr : (essentialFactor P x).denom.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (essentialFactor P x) *
      (∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)).eval z = 1 := by
  let D : Polynomial ℂ := ∏ i, P.comp (Polynomial.C (x i : ℂ) * Polynomial.X)
  have hD : algebraMap (Polynomial ℂ) RationalFunctions D ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (Polynomial ℂ) RationalFunctions).ne
        (specializedCoordinateDenominator_ne_zero P hP x)
  have he : essentialFactor P x * algebraMap (Polynomial ℂ) RationalFunctions D = 1 := by
    rw [essentialFactor_eq]
    exact inv_mul_cancel₀ hD
  have hh := congrArg (RatFunc.eval (RingHom.id ℂ) z) he
  rw [RatFunc.eval_mul _ _ (by simpa using hr) (by simp),
    RatFunc.eval_algebraMap, RatFunc.eval_one] at hh
  simpa only [Polynomial.eval₂_id, Algebra.algebraMap_self, RingHom.id_apply] using hh

section Essential

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable (w : (coefficientModel π ℓ).toSubmodule)

/-- The actual model series has numerator one when the essential identity holds. -/
theorem corankOneModelDenominatorProduct_eq_one_of_essentialIdentity
    (P : Polynomial ℂ) (hP : P.coeff 0 = 1)
    (hid : SatisfiesEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P w.val) :
    corankOneModelDenominatorProduct h π hπ ℓ w P = 1 := by
  apply HahnSeries.ext
  funext d
  apply symmetricTorus_eq_of_evaluations
  intro x
  let S := corankOneModelDenominatorProduct h π hπ ℓ w P
  let ev := symmetricTorusEvaluation (Fin (n + 1)) ℂ x
  let c : ℤ → ℂ := fun e => ev ((S - 1).coeff e)
  have hcbelow : ∃ b : ℤ, ∀ e < b, c e = 0 := by
    obtain ⟨b, hb⟩ := corankOneModelDenominatorProduct_coeff_eq_zero_below h π hπ ℓ w
    refine ⟨min b 0, fun e he => ?_⟩
    have he0 : e ≠ 0 := by omega
    simp only [c, HahnSeries.coeff_sub, S, hb P e (by omega),
      HahnSeries.coeff_one, ite_eq_right he0, sub_zero, map_zero]
  obtain ⟨b, hb⟩ := hcbelow
  obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := hid x
  let A := max a a'
  have hq1 : (1 : ℝ) < q := by exact_mod_cast h.one_lt_q
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hc : c d = 0 := by
    refine eq_zero_of_hasSum_int_eq_zero hb (Real.rpow_pos_of_pos hq0 (-A)) ?_ d
    intro X hX hXr
    let s : ℝ := -Real.log X / Real.log q
    have hs : A < s := by
      have h1 := Real.log_lt_log hX hXr
      rw [Real.log_rpow hq0] at h1
      dsimp only [s]
      rw [lt_div_iff₀ hlogq]
      linarith
    have hXs : spectralPoint q (s : ℂ) = (X : ℂ) := by
      rw [spectralPoint_ofReal, Real.rpow_def_of_pos hq0]
      have hm : Real.log q * -s = Real.log X := by
        dsimp only [s]
        field_simp
      rw [hm, Real.exp_log hX]
    have hconv := ha (s : ℂ) (lt_of_le_of_lt (le_max_left _ _) hs)
    have hcont := ha' (s : ℂ) (lt_of_le_of_lt (le_max_right _ _) hs)
    have hsum := hasSum_corankOneIntegral h w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) (s : ℂ) hconv
    rw [hXs] at hsum
    have hsum' : HasSum (fun e : ℤ =>
        ev ((corankOneModelLaurentSeries h π hπ ℓ w).coeff e) * (X : ℂ) ^ e)
        (corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) (s : ℂ)) := by
      convert hsum using 1
      funext e
      rw [corankOneModelLaurentSeries_coeff, mul_comm,
        symmetricTorusEvaluation_degreeCorankOneModelCoefficient]
    have hmul := hasSum_mapped_laurent_mul_polynomial ev.toRingHom
      (corankOneModelLaurentSeries h π hπ ℓ w)
      (Complex.ofReal_ne_zero.mpr hX.ne') hsum'
      (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P)
    have heval : corankOneIntegral ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) (s : ℂ) *
        ((coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P).map ev.toRingHom).eval
          (X : ℂ) = 1 := by
      rw [Polynomial.eval_map, coordinateDenominatorPolynomial_eval₂]
      rw [hcont.2, hXs]
      have hh := essentialFactor_eval_mul_denominator P hP x (X : ℂ) (by
        simpa only [hXs] using hcont.1)
      simpa only [Polynomial.eval_prod, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, mul_comm] using hh
    rw [heval] at hmul
    have hmul' : HasSum (fun e : ℤ => ev (S.coeff e) * (X : ℂ) ^ e) 1 := by
      exact hmul
    have hsingle : HasSum (fun e : ℤ => ev ((1 : LaurentSeries _).coeff e) *
        (X : ℂ) ^ e) 1 := by
      convert (hasSum_ite_eq (0 : ℤ) (1 : ℂ)) using 1
      funext e
      by_cases he : e = 0 <;> simp [HahnSeries.coeff_one, he]
    have hsub := hmul'.sub hsingle
    rw [sub_self] at hsub
    convert hsub using 1
    funext e
    simp only [c, HahnSeries.coeff_sub, map_sub, sub_mul]
  change ev (S.coeff d) = ev ((1 : LaurentSeries _).coeff d)
  change ev ((S - 1).coeff d) = 0 at hc
  simpa only [HahnSeries.coeff_sub, map_sub, sub_eq_zero] using hc

/-- The essential identity forces actual polynomial Satake coefficients. -/
theorem degreeCorankOneModelCoefficient_mem_polynomial_of_essentialIdentity
    (P : Polynomial ℂ) (hP : P.coeff 0 = 1)
    (hid : SatisfiesEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P w.val)
    (d : ℤ) :
    degreeCorankOneModelCoefficient h π hπ ℓ w d ∈
      symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ := by
  classical
  obtain ⟨b, hb⟩ := degreeCorankOneModelCoefficient_eq_zero_below h π hπ ℓ w
  have hc (m : ℕ) :
      (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P).coeff m ∈
        symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ := by
    rw [coordinateDenominatorPolynomial_coeff]
    exact (symmetricPolynomialToTorus (Fin (n + 1)) ℂ).mem_range_self _
  have hP0 := coordinateDenominatorPolynomial_coeff_zero (Fin (n + 1)) ℂ P hP
  have h0 : 0 ∈ (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P).support := by
    rw [Polynomial.mem_support_iff, hP0]
    intro he
    have he' := congrArg
      (symmetricTorusEvaluation (Fin (n + 1)) ℂ (fun _ => 1)) he
    exact one_ne_zero (by simpa only [map_one, map_zero] using he')
  have hrec (e : ℤ) :
      degreeCorankOneModelCoefficient h π hπ ℓ w e +
        ∑ m ∈ (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P).support.erase 0,
          degreeCorankOneModelCoefficient h π hπ ℓ w (e - (m : ℤ)) *
            (coordinateDenominatorPolynomial (Fin (n + 1)) ℂ P).coeff m =
      if e = 0 then 1 else 0 := by
    have he := congrArg
      (fun T : LaurentSeries (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) => T.coeff e)
      (corankOneModelDenominatorProduct_eq_one_of_essentialIdentity h π hπ ℓ w P hP hid)
    rw [corankOneModelDenominatorProduct_coeff] at he
    simp only [← coordinateDenominatorPolynomial_coeff] at he
    rw [← Finset.add_sum_erase _ _ h0] at he
    by_cases he0 : e = 0
    · simpa only [Int.natCast_zero, sub_zero, hP0, mul_one, HahnSeries.coeff_one,
        ite_eq_left he0] using he
    · simpa only [Int.natCast_zero, sub_zero, hP0, mul_one, HahnSeries.coeff_one,
        ite_eq_right he0] using he
  have step (e : ℤ)
      (ih : ∀ e' < e, degreeCorankOneModelCoefficient h π hπ ℓ w e' ∈
        symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ) :
      degreeCorankOneModelCoefficient h π hπ ℓ w e ∈
        symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ := by
    rw [eq_sub_of_add_eq (hrec e)]
    rw [sub_eq_add_neg, ← neg_one_smul ℂ]
    apply (symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ).add_mem
    · split_ifs <;> simp only [Subalgebra.one_mem, Subalgebra.zero_mem]
    · apply (symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ).smul_mem
      apply (symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ).sum_mem
      intro m hm
      have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
      exact (symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ).mul_mem
        (ih (e - (m : ℤ)) (by omega)) (hc m)
  have hm (k : ℕ) : ∀ e : ℤ, e < b + (k : ℤ) →
      degreeCorankOneModelCoefficient h π hπ ℓ w e ∈
        symmetricPolynomialTorusSubalgebra (Fin (n + 1)) ℂ := by
    induction k with
    | zero =>
        intro e he
        rw [hb e (by simpa using he)]
        exact Subalgebra.zero_mem _
    | succ k ih =>
        intro e he
        by_cases he' : e < b + (k : ℤ)
        · exact ih e he'
        · exact step e (fun e' he' => ih e' (by omega))
  by_cases hd : d < b
  · rw [hb d hd]
    exact Subalgebra.zero_mem _
  · apply hm ((d - b).toNat + 1) d
    have he : ((d - b).toNat : ℤ) = d - b := Int.toNat_of_nonneg (by omega)
    push_cast
    omega

/-- A version in the ordinary polynomial ring, for the Schur obstruction. -/
theorem degreeCorankOneModelCoefficient_eq_polynomial_of_essentialIdentity
    (P : Polynomial ℂ) (hP : P.coeff 0 = 1)
    (hid : SatisfiesEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P w.val)
    (d : ℤ) :
    ∃ p : MvPolynomial (Fin (n + 1)) ℂ,
      algebraMap (MvPolynomial (Fin (n + 1)) ℂ)
        (TorusPolynomialAlgebra (Fin (n + 1)) ℂ) p =
      (degreeCorankOneModelCoefficient h π hπ ℓ w d).val := by
  obtain ⟨p, hp⟩ := (symmetricPolynomialToTorus (Fin (n + 1)) ℂ).mem_range.mp
    (degreeCorankOneModelCoefficient_mem_polynomial_of_essentialIdentity
      h π hπ ℓ w P hP hid d)
  exact ⟨p.val, congrArg Subtype.val hp⟩

end Essential

end Langlands.Conductor
