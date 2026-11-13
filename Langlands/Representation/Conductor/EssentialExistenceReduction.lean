import Langlands.Representation.Conductor.SphericalUniformBound
import Langlands.Representation.Conductor.SphericalNumeratorIdeal
import Langlands.Representation.Conductor.EssentialRestrictionUniqueness
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.RankinSelberg.RationalEvaluation

/-!
# Existence of the essential vector from the JPSS inputs

Jacquet 2012, sections 1-2: for a smooth `π` of `GL_(n+2)(F)` with standard L-polynomial
`P`, the Whittaker model of `ℓ` contains an essential vector once three inputs are given
for every tuple of units `x`. They are the JPSS 1983 facts that Jacquet uses: the
corank-one integrals against `W(g; x; ψ̄)` converge on a right half-plane, their products
with `∏ P(x_i q^(-s))` are Laurent polynomials in `q^(-s)`, and Jacquet's Lemma 4 holds.
They are hypotheses here. Following Jacquet, the numerators `Ξ(W)` form an ideal of
symmetric Laurent polynomials with no common zero, so some `W` has `Ξ(W) = 1`. Averaging
that `W` over `diag(GL_(n+1)(O), 1)` keeps its Laurent series and adds the
restriction-invariance clause.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Polynomial Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg Langlands.QuotientIntegration
open Langlands.GeneralLinear.Iwasawa
open scoped BigOperators

universe uF uV

section Laurent

/-- Multiplying a convergent Laurent sum by a polynomial convolves its coefficients. -/
theorem hasSum_polynomial_eval_mul {c : ℤ → ℂ} {y f : ℂ} (hy : y ≠ 0) (Q : ℂ[X])
    (h : HasSum (fun d : ℤ => y ^ d * c d) f) :
    HasSum (fun e : ℤ => (∑ m ∈ Q.support, c (e - m) * Q.coeff m) * y ^ e)
      (Q.eval y * f) := by
  have hterm : ∀ m ∈ Q.support, HasSum (fun e : ℤ => c (e - m) * Q.coeff m * y ^ e)
      (Q.coeff m * y ^ m * f) := by
    intro m _
    have h2 := (Equiv.subRight (m : ℤ)).hasSum_iff.mpr (h.mul_left (Q.coeff m * y ^ m))
    convert h2 using 1
    funext e
    simp only [Function.comp_apply, Equiv.subRight_apply]
    have hpow : y ^ e = y ^ m * y ^ (e - m) := by
      rw [← zpow_natCast, ← zpow_add₀ hy, add_sub_cancel]
    rw [hpow]
    ring
  convert hasSum_sum hterm using 1
  · funext e
    rw [Finset.sum_mul]
  · rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]

/-- Shifting the coefficients of a convergent Laurent sum multiplies it by a power. -/
theorem hasSum_coeff_shift {T : ℤ → ℂ} {y g : ℂ} (hy : y ≠ 0) (k : ℤ)
    (h : HasSum (fun e : ℤ => T e * y ^ e) g) :
    HasSum (fun e : ℤ => T (e - k) * y ^ e) (y ^ k * g) := by
  have h1 := (Equiv.subRight k).hasSum_iff.mpr (h.mul_left (y ^ k))
  convert h1 using 1
  funext e
  simp only [Function.comp_apply, Equiv.subRight_apply]
  have hpow : y ^ e = y ^ k * y ^ (e - k) := by
    rw [← zpow_add₀ hy, add_sub_cancel]
  rw [hpow]
  ring

/-- A monomial times a polynomial is a finite Laurent sum. -/
theorem hasSum_monomial_mul_polynomial {y : ℂ} (hy : y ≠ 0) (N : ℤ) (Q : ℂ[X]) :
    HasSum (fun e : ℤ => (if N ≤ e then Q.coeff (e - N).toNat else 0) * y ^ e)
      (y ^ N * Q.eval y) := by
  have hinj : Function.Injective (fun k : ℕ => N + (k : ℤ)) := by
    intro a b hab
    simpa using hab
  rw [← hinj.hasSum_iff]
  · have hfin : HasSum (fun k : ℕ => Q.coeff k * y ^ k) (Q.eval y) := by
      rw [Polynomial.eval_eq_sum_range]
      apply hasSum_sum_of_ne_finset_zero
      intro k hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hk), zero_mul]
    convert hfin.mul_left (y ^ N) using 1
    funext k
    simp only [Function.comp_apply, le_add_iff_nonneg_right, Nat.cast_nonneg, ite_true,
      add_sub_cancel_left, Int.toNat_natCast]
    rw [zpow_add₀ hy, zpow_natCast]
    ring
  · intro e he
    have hlt : ¬ N ≤ e := by
      intro hle
      apply he
      refine ⟨(e - N).toNat, ?_⟩
      change N + ((e - N).toNat : ℤ) = e
      omega
    simp only [hlt, ite_false, zero_mul]

/-- A Laurent series with lower-bounded support whose sums on an interval `(0, r)` are
those of `y^N Q(y)` vanishes above degree `N + deg Q`. -/
theorem coeff_eq_zero_above_of_hasSum_eq {c : ℤ → ℂ} {d₀ : ℤ} (hc : ∀ d < d₀, c d = 0)
    {r : ℝ} (hr : 0 < r) (N : ℤ) (Q : ℂ[X])
    (hsum : ∀ y : ℝ, 0 < y → y < r →
      HasSum (fun d : ℤ => c d * (y : ℂ) ^ d) ((y : ℂ) ^ N * Q.eval (y : ℂ))) :
    ∀ d, N + Q.natDegree < d → c d = 0 := by
  intro d hd
  have hdiff := eq_zero_of_hasSum_int_eq_zero
    (c := fun e => c e - (if N ≤ e then Q.coeff (e - N).toNat else 0)) (d₀ := min d₀ N)
    (fun e he => by
      have h1 : ¬ N ≤ e := by omega
      simp only [hc e (by omega), h1, ite_false, sub_zero])
    hr (fun y hy hyr => by
      have h2 := (hsum y hy hyr).sub
        (hasSum_monomial_mul_polynomial (Complex.ofReal_ne_zero.mpr hy.ne') N Q)
      rw [sub_self] at h2
      convert h2 using 1
      funext e
      ring) d
  have hR : Q.coeff (d - N).toNat = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simpa only [show N ≤ d by omega, ite_true, hR, sub_zero] using hdiff

/-- A real point of `(0, q^(-a))` is the spectral point of a real `s > a`. -/
theorem exists_spectralPoint_eq {q : ℕ} (hq : 1 < q) (a : ℝ) {y : ℝ} (hy : 0 < y)
    (hyr : y < (q : ℝ) ^ (-a)) :
    ∃ s : ℝ, a < s ∧ spectralPoint q (s : ℂ) = (y : ℂ) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  refine ⟨-Real.log y / Real.log q, ?_, ?_⟩
  · have h1 : Real.log y < Real.log ((q : ℝ) ^ (-a)) := Real.log_lt_log hy hyr
    rw [Real.log_rpow hq0] at h1
    rw [lt_div_iff₀ hlogq]
    linarith
  · have hrpow : (q : ℝ) ^ (-(-Real.log y / Real.log q)) = y := by
      rw [Real.rpow_def_of_pos hq0]
      have hl : Real.log q ≠ 0 := hlogq.ne'
      have hm : Real.log q * -(-Real.log y / Real.log q) = Real.log y := by
        field_simp
      rw [hm, Real.exp_log hy]
    rw [spectralPoint_ofReal, hrpow]

end Laurent

section Residue

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A lift to `F` of each residue class of the valuation ring. -/
def residueClassLift (r : IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) : F :=
  ((Function.surjInv (IsLocalRing.residue_surjective
    (R := (ValuativeRel.valuation F).integer)) r : (ValuativeRel.valuation F).integer) : F)

theorem residueClassLift_mem (r : IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) :
    residueClassLift r ∈ (ValuativeRel.valuation F).integer :=
  (Function.surjInv (IsLocalRing.residue_surjective
    (R := (ValuativeRel.valuation F).integer)) r).property

theorem residue_surjInv (r : IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) :
    IsLocalRing.residue (ValuativeRel.valuation F).integer
      (Function.surjInv (IsLocalRing.residue_surjective
        (R := (ValuativeRel.valuation F).integer)) r) = r :=
  Function.surjInv_eq _ r

theorem residue_eq_zero_iff_valuation_lt_one (z : (ValuativeRel.valuation F).integer) :
    IsLocalRing.residue (ValuativeRel.valuation F).integer z = 0 ↔
      ValuativeRel.valuation F (z : F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

/-- Distinct residue classes have lifts at valuation one. -/
theorem residueClassLift_eq_of_lt_one
    {r t : IsLocalRing.ResidueField (ValuativeRel.valuation F).integer}
    (h : ValuativeRel.valuation F (residueClassLift r - residueClassLift t) < 1) : r = t := by
  have h0 := (residue_eq_zero_iff_valuation_lt_one
    (Function.surjInv (IsLocalRing.residue_surjective
        (R := (ValuativeRel.valuation F).integer)) r -
      Function.surjInv (IsLocalRing.residue_surjective
        (R := (ValuativeRel.valuation F).integer)) t)).2 h
  rw [map_sub, residue_surjInv, residue_surjInv, sub_eq_zero] at h0
  exact h0

/-- Every integral element is congruent to the lift of its residue class. -/
theorem exists_residueClassLift_lt_one {z : F} (hz : z ∈ (ValuativeRel.valuation F).integer) :
    ∃ r, ValuativeRel.valuation F (z - residueClassLift r) < 1 := by
  refine ⟨IsLocalRing.residue (ValuativeRel.valuation F).integer ⟨z, hz⟩, ?_⟩
  exact (residue_eq_zero_iff_valuation_lt_one (⟨z, hz⟩ - Function.surjInv
    (IsLocalRing.residue_surjective (R := (ValuativeRel.valuation F).integer))
      (IsLocalRing.residue (ValuativeRel.valuation F).integer ⟨z, hz⟩))).1
    (by rw [map_sub, residue_surjInv, sub_self])

omit [IsNonarchimedeanLocalField F] in
/-- For `ψ` of conductor `O`, every adjacent root subgroup meets `ϖ⁻¹ O` in a point where
the inverse standard character is nontrivial. -/
theorem exists_adjacentUnit_ne_one {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ)
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n : ℕ) (i : Fin n) :
    ∃ x : F, ValuativeRel.valuation F x * ValuativeRel.valuation F (ϖ : F) ≤ 1 ∧
      inverseStandardCharacter ψ n (UpperUnipotentCharacter.adjacentUnit i x) ≠ 1 := by
  have hinv : ValuativeRel.valuation F ((ϖ : F)⁻¹) * ValuativeRel.valuation F (ϖ : F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (Units.ne_zero ϖ), map_one]
  have hnot : (ϖ : F)⁻¹ ∉ (ValuativeRel.valuation F).integer := by
    intro hmem
    have hle : ValuativeRel.valuation F ((ϖ : F)⁻¹) ≤ 1 := hmem
    have h1 : (1 : _) ≤ ValuativeRel.valuation F (ϖ : F) := by
      calc (1 : _) = ValuativeRel.valuation F ((ϖ : F)⁻¹) * ValuativeRel.valuation F (ϖ : F) :=
            hinv.symm
        _ ≤ 1 * ValuativeRel.valuation F (ϖ : F) := mul_le_mul_left hle _
        _ = ValuativeRel.valuation F (ϖ : F) := one_mul _
    exact absurd hϖ.1 (not_lt.mpr h1)
  have hex : ∃ y ∈ (ValuativeRel.valuation F).integer, ψ ((ϖ : F)⁻¹ * y) ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hnot (hψ.2 _ hall)
  obtain ⟨y, hy, hψy⟩ := hex
  refine ⟨(ϖ : F)⁻¹ * y, ?_, ?_⟩
  · have hy' : ValuativeRel.valuation F y ≤ 1 := hy
    calc ValuativeRel.valuation F ((ϖ : F)⁻¹ * y) * ValuativeRel.valuation F (ϖ : F)
        = (ValuativeRel.valuation F ((ϖ : F)⁻¹) * ValuativeRel.valuation F (ϖ : F)) *
            ValuativeRel.valuation F y := by rw [map_mul, mul_right_comm]
      _ = ValuativeRel.valuation F y := by rw [hinv, one_mul]
      _ ≤ 1 := hy'
  · intro heq
    apply hψy
    have hval := congrArg (fun u : ℂˣ => (u : ℂ)) heq
    simp only [inverseStandardCharacter, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
      Units.val_one] at hval
    rw [standardCharacter_adjacentUnit_val, inv_eq_one, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
      Circle.coe_eq_one] at hval
    exact hval

end Residue

section Model

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
variable (P : ℂ[X])

/-- Jacquet's ideal step (section 2, end), with the residue-class inputs supplied by the
local field: if at every tuple of units some model vector with a finite numerator has a
nonvanishing numerator value, some model vector has numerator one. -/
theorem exists_corankOneModelNumerator_eq_one
    (hnonzero : ∀ x : Fin (n + 1) → ℂˣ,
      ∃ (w : (coefficientModel π ℓ).toSubmodule)
        (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite),
        symmetricTorusEvaluation (Fin (n + 1)) ℂ x
          (corankOneModelNumerator h π hπ ℓ w P hw) ≠ 0) :
    ∃ (w : (coefficientModel π ℓ).toSubmodule)
      (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite),
      corankOneModelNumerator h π hπ ℓ w P hw = 1 := by
  classical
  let : Fintype (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) :=
    Fintype.ofFinite _
  exact exists_corankOneModelNumerator_eq_one_of_no_common_zero h π hπ ℓ
    (lt_trans zero_lt_one h.one_lt_q)
    (by rw [h.residueCardinality, Nat.card_eq_fintype_card])
    (exists_adjacentUnit_ne_one h.conductor h.uniformizer n) residueClassLift
    residueClassLift_mem (fun _ _ hrt => residueClassLift_eq_of_lt_one hrt)
    (fun _ hz => exists_residueClassLift_lt_one hz) P hnonzero

/-- Where the corank-one integral converges, multiplying it by `∏ P(x_i q^(-s))` gives
the Laurent sum of the specialized model denominator product. -/
theorem hasSum_specializedDenominatorProduct (w : (coefficientModel π ℓ).toSubmodule)
    (x : Fin (n + 1) → ℂˣ) (s : ℂ)
    (hconv : CorankOneConverges ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) :
    HasSum (fun e : ℤ => ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
        (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff e * spectralPoint q s ^ e)
      ((∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) *
        corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) := by
  have hq : 0 < q := lt_trans zero_lt_one h.one_lt_q
  have h1 := hasSum_polynomial_eval_mul (spectralPoint_ne_zero_of_pos hq s)
    (∏ i, P.comp (C (x i : ℂ) * X)) (hasSum_corankOneIntegral h w.val _ s hconv)
  convert h1 using 1
  funext e
  congr 1
  rw [corankOneModelDenominatorProduct_specialize, mul_finitePolynomialLaurentSeries_coeff]
  simp only [specializedCorankOneModelLaurentSeries_coeff]

/-- **Pointwise finiteness from JPSS.** If the corank-one integral converges on a right
half-plane and its product with `∏ P(x_i q^(-s))` is `q^(-Ns) Q(q^(-s))` there, the
specialized model denominator product vanishes above degree `N + deg Q`. -/
theorem specializedDenominatorProduct_exists_upper_bound
    (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ)
    (hconv : ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    (hpoly : ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
      corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s *
        (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
      spectralPoint q s ^ N * Q.eval (spectralPoint q s)) :
    ∃ B : ℤ, ∀ d, B < d → ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
      (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d = 0 := by
  obtain ⟨a₁, ha₁⟩ := hconv
  obtain ⟨a₂, N, Q, ha₂⟩ := hpoly
  obtain ⟨d₀, hd₀⟩ := corankOneModelDenominatorProduct_coeff_eq_zero_below h π hπ ℓ w
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one h.one_lt_q
  refine ⟨N + Q.natDegree, coeff_eq_zero_above_of_hasSum_eq (d₀ := d₀) (fun d hd => ?_)
    (Real.rpow_pos_of_pos hq0 (-(max a₁ a₂))) N Q (fun y hy hyr => ?_)⟩
  · change symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      ((corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d) = 0
    rw [hd₀ P d hd, map_zero]
  · obtain ⟨s, hs, hsy⟩ := exists_spectralPoint_eq h.one_lt_q (max a₁ a₂) hy hyr
    have hs1 : a₁ < (s : ℂ).re := by
      rw [Complex.ofReal_re]
      exact lt_of_le_of_lt (le_max_left _ _) hs
    have hs2 : a₂ < (s : ℂ).re := by
      rw [Complex.ofReal_re]
      exact lt_of_le_of_lt (le_max_right _ _) hs
    have hsum := hasSum_specializedDenominatorProduct h π hπ ℓ P w x s (ha₁ s hs1)
    have heq := ha₂ s hs2
    rw [mul_comm (corankOneIntegral _ _ _ _ _ _)] at heq
    rw [heq, hsy] at hsum
    exact hsum

/-- **Finite support from JPSS.** If every corank-one integral of `w` has the two
properties above for every tuple of units, the actual model denominator product of `w`
has finite support over the symmetric Laurent algebra. -/
theorem corankOneModelDenominatorProduct_support_finite_of_jpss
    (w : (coefficientModel π ℓ).toSubmodule)
    (hconv : ∀ x : Fin (n + 1) → ℂˣ, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    (hpoly : ∀ x : Fin (n + 1) → ℂˣ, ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
      corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s *
        (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
      spectralPoint q s ^ N * Q.eval (spectralPoint q s)) :
    (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite :=
  corankOneModelDenominatorProduct_support_finite_of_pointwise h π hπ ℓ w P
    (fun x => specializedDenominatorProduct_exists_upper_bound h π hπ ℓ P w x
      (hconv x) (hpoly x))

/-- **Jacquet's Lemma 4 at `X = 1`.** If `∑_j q^(-e_j s) Ψ(s, W_j, W(x)) ∏ P(x_i q^(-s)) = 1`
on a right half-plane where every integral converges, the numerators of the `W_j`
(evaluated at `x`) add up to one. -/
theorem sum_numerator_evaluation_eq_one (x : Fin (n + 1) → ℂˣ) {k : ℕ}
    (W : Fin k → (coefficientModel π ℓ).toSubmodule) (e : Fin k → ℤ)
    (hfin : ∀ j, (corankOneModelDenominatorProduct h π hπ ℓ (W j) P).support.Finite)
    (hconv : ∀ j, ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ (W j).val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    (hgen : ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      (∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) *
        (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1) :
    ∑ j, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (corankOneModelNumerator h π hπ ℓ (W j) P (hfin j)) = 1 := by
  classical
  set Qx : ℂ[X] := ∏ i, P.comp (C (x i : ℂ) * X) with hQx
  set U : Fin k → ℤ → ℂ := fun j d => ((corankOneModelDenominatorProduct h π hπ ℓ (W j) P).map
    (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d with hU
  choose d₀ hd₀ using fun j => corankOneModelDenominatorProduct_coeff_eq_zero_below h π hπ ℓ (W j)
  have hUbelow : ∀ j d, d < d₀ j → U j d = 0 := by
    intro j d hd
    change symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      ((corankOneModelDenominatorProduct h π hπ ℓ (W j) P).coeff d) = 0
    rw [hd₀ j P d hd, map_zero]
  have hUsupp : ∀ j, Function.support (U j) ⊆ ((hfin j).toFinset : Set ℤ) := by
    intro j d hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, HahnSeries.mem_support]
    intro hz
    apply hd
    change symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      ((corankOneModelDenominatorProduct h π hπ ℓ (W j) P).coeff d) = 0
    rw [hz, map_zero]
  have hcoeff : ∀ t : ℤ, ∑ j, U j (t - e j) = if t = 0 then 1 else 0 := by
    obtain ⟨a, ha⟩ := hgen
    choose b hb using hconv
    set A : ℝ := max a (∑ j, |b j|) with hA
    have hbA : ∀ j, b j < A + 1 := by
      intro j
      have h1 := Finset.single_le_sum (f := fun j => |b j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)
      have h2 := le_abs_self (b j)
      have h3 := le_max_right a (∑ j, |b j|)
      linarith
    have haA : a < A + 1 := by
      have := le_max_left a (∑ j, |b j|)
      linarith
    have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one h.one_lt_q
    intro t
    have key := eq_zero_of_hasSum_int_eq_zero
      (c := fun t => (∑ j, U j (t - e j)) - (if t = 0 then (1 : ℂ) else 0))
      (d₀ := -∑ j, |d₀ j + e j|) (fun t ht => ?_)
      (Real.rpow_pos_of_pos hq0 (-(A + 1))) (fun y hy hyr => ?_) t
    · exact sub_eq_zero.mp key
    · have hle : ∀ j, -∑ j, |d₀ j + e j| ≤ d₀ j + e j := by
        intro j
        have h1 := Finset.single_le_sum (f := fun j => |d₀ j + e j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 := neg_abs_le (d₀ j + e j)
        linarith
      have hnonpos : -∑ j, |d₀ j + e j| ≤ 0 := by
        have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (d₀ j + e j))
        linarith
      have ht0 : t ≠ 0 := by
        intro h0
        rw [h0] at ht
        linarith
      simp only [ht0, ite_false, sub_zero]
      apply Finset.sum_eq_zero
      intro j _
      apply hUbelow
      linarith [hle j]
    · obtain ⟨s, hs, hsy⟩ := exists_spectralPoint_eq h.one_lt_q (A + 1) hy hyr
      have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have hsum : ∀ j ∈ (Finset.univ : Finset (Fin k)), HasSum (fun t => U j (t - e j) * (y : ℂ) ^ t)
          ((y : ℂ) ^ e j * (Qx.eval (y : ℂ) * corankOneIntegral ψ abv μ (W j).val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)) := by
        intro j _
        have h1 := hasSum_specializedDenominatorProduct h π hπ ℓ P (W j) x s
          (hb j s (by rw [Complex.ofReal_re]; linarith [hbA j]))
        rw [hsy] at h1
        exact hasSum_coeff_shift hy0 (e j) h1
      have htot := hasSum_sum hsum
      have hval := ha s (by rw [Complex.ofReal_re]; linarith)
      rw [hsy] at hval
      have hval' : ∑ j, (y : ℂ) ^ e j * (Qx.eval (y : ℂ) * corankOneIntegral ψ abv μ (W j).val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) = 1 := by
        rw [← hval, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hval'] at htot
      have hdelta : HasSum (fun t : ℤ => (if t = 0 then (1 : ℂ) else 0) * (y : ℂ) ^ t) 1 := by
        convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 1
        funext t
        split_ifs with ht
        · rw [ht, zpow_zero, mul_one]
        · rw [zero_mul]
      have hdiff := htot.sub hdelta
      rw [sub_self] at hdiff
      convert hdiff using 1
      funext t
      rw [sub_mul, Finset.sum_mul]
  have hNj : ∀ j, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (corankOneModelNumerator h π hπ ℓ (W j) P (hfin j)) = ∑ᶠ t, U j (t - e j) := by
    intro j
    rw [corankOneModelNumerator_evaluation,
      show (∑ᶠ t, U j (t - e j)) = ∑ᶠ t, U j t from
        finsum_comp_equiv (Equiv.subRight (e j)) (f := U j),
      finsum_eq_sum_of_support_subset _ (hUsupp j)]
  simp_rw [hNj]
  rw [← finsum_sum_comm]
  · simp_rw [hcoeff]
    rw [finsum_eq_single _ (0 : ℤ) (fun t ht => by simp [ht])]
    simp
  · intro j _
    have hf : (Function.support (U j)).Finite :=
      (Finset.finite_toSet _).subset (hUsupp j)
    exact (hf.preimage (Set.injOn_of_injective (sub_left_injective (b := e j))))

/-- **Numerator one.** If the numerator of `w` is one, then for every tuple of units the
specialized model denominator product is the constant series one. -/
theorem specializedDenominatorProduct_coeff_of_numerator_eq_one
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (h1 : corankOneModelNumerator h π hπ ℓ w P hw = 1) (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
      (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d = if d = 0 then 1 else 0 := by
  classical
  obtain ⟨d₀, hd₀⟩ := corankOneModelDenominatorProduct_coeff_eq_zero_below h π hπ ℓ w
  have key := eq_zero_of_hasSum_int_eq_zero
    (c := fun d => ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
      (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d - if d = 0 then 1 else 0)
    (d₀ := min d₀ 0) (fun d hd => ?_) one_pos (fun y hy _ => ?_) d
  · exact sub_eq_zero.mp key
  · have h0 : d ≠ 0 := by omega
    simp only [h0, ite_false, sub_zero]
    change symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      ((corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d) = 0
    rw [hd₀ P d (by omega), map_zero]
  · have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hscale := symmetricTorusEvaluation_finiteLaurentCoefficientSum_scale (Fin (n + 1)) ℂ
      (corankOneModelDenominatorProduct h π hπ ℓ w P) hw
      (corankOneModelDenominatorProduct_coeff_isHomogeneous h π hπ ℓ w P) x (Units.mk0 _ hy0)
    change symmetricTorusEvaluation (Fin (n + 1)) ℂ _
      (corankOneModelNumerator h π hπ ℓ w P hw) = _ at hscale
    rw [h1, map_one] at hscale
    have hA : HasSum (fun d : ℤ => ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
        (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d * (y : ℂ) ^ d) 1 := by
      have hfs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ)
        (s := hw.toFinset)
        (f := fun d : ℤ => ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
          (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d * (y : ℂ) ^ d) (by
        intro d hd
        rw [Set.Finite.mem_toFinset, HahnSeries.mem_support, not_not] at hd
        change symmetricTorusEvaluation (Fin (n + 1)) ℂ x
          ((corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d) * _ = 0
        rw [hd, map_zero, zero_mul])
      rw [hscale]
      convert hfs using 1
      apply Finset.sum_congr rfl
      intro d _
      rw [Units.val_mk0, mul_comm]
    have hB : HasSum (fun d : ℤ => (if d = 0 then (1 : ℂ) else 0) * (y : ℂ) ^ d) 1 := by
      convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 1
      funext t
      split_ifs with ht
      · rw [ht, zpow_zero, mul_one]
      · rw [zero_mul]
    have hdiff := hA.sub hB
    rw [sub_self] at hdiff
    convert hdiff using 1
    funext d
    ring

/-- **The identity.** If the specialized model denominator product at `x` is one and the
corank-one integral converges on a right half-plane, the integral has the rational
continuation `∏ P(x_i X)⁻¹` of Jacquet's Theorem 1. -/
theorem hasRationalContinuation_essentialFactor_of_coeff
    (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ)
    (hconv : ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    (hδ : ∀ d, ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
      (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d = if d = 0 then 1 else 0) :
    HasRationalContinuation q (corankOneIntegral ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)) (essentialFactor P x) := by
  classical
  obtain ⟨a, ha⟩ := hconv
  refine ⟨a, fun s hs => ?_⟩
  have hsum := hasSum_specializedDenominatorProduct h π hπ ℓ P w x s (ha s hs)
  simp only [hδ] at hsum
  have hone : HasSum (fun e : ℤ => (if e = 0 then (1 : ℂ) else 0) * spectralPoint q s ^ e) 1 := by
    convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 1
    funext t
    split_ifs with ht
    · rw [ht, zpow_zero, mul_one]
    · rw [zero_mul]
  have heq := hsum.unique hone
  have hQ : (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) ≠ 0 :=
    left_ne_zero_of_mul_eq_one heq
  have hev : RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
      (algebraMap ℂ[X] RationalFunctions (∏ i, P.comp (C (x i : ℂ) * X))) =
      (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) := by
    rw [RatFunc.eval_algebraMap]
    simp
  rw [essentialFactor_eq]
  refine ⟨RationalEvaluation.RegularAt.inv (by rw [hev]; exact hQ), ?_⟩
  rw [RationalEvaluation.eval_inv (by rw [hev]; exact hQ), hev]
  exact eq_inv_of_mul_eq_one_right heq

end Model

section Averaging

/-- A linear map that is invariant under a representation takes the mean of a finite
orbit to its value at the original vector. -/
theorem linearMap_orbitMean_eq {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G E) (f : E →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = f v) (v : E) [Finite (Compact.orbit ρ v)] :
    f (Compact.orbitMean ρ v) = f v := by
  have hfin : Finite (Compact.orbit (Representation.trivial ℂ G W) (f v)) := by
    apply Set.Finite.to_subtype
    apply (Set.finite_singleton (f v)).subset
    rintro _ ⟨g, rfl⟩
    simp [Representation.trivial_apply]
  rw [Compact.orbitMean_map ρ (Representation.trivial ℂ G W) f
    (fun g u => by rw [hf, Representation.trivial_apply]) v]
  exact Compact.orbitMean_id _ _ (fun g => Representation.trivial_apply ℂ g (f v))

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

/-- Translating a model vector by `diag(k, 1)` with `k ∈ GL_(n+1)(O)` does not change
its Laurent degree coefficients: `W(g; x; ψ̄)`, `|det g|` and the degree are right
`GL_(n+1)(O)`-invariant, and so is the quotient measure. -/
theorem degreeCorankOneModelCoefficient_integral_translate
    (k : Langlands.GeneralLinear (n + 1) F)
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n)
    (u : (coefficientModel π ℓ).toSubmodule) (d : ℤ) :
    degreeCorankOneModelCoefficient h π hπ ℓ (modelRepresentation π ℓ (rankInclusion 1 k) u) d =
      degreeCorankOneModelCoefficient h π hπ ℓ u d := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_degreeCorankOneModelCoefficient,
    symmetricTorusEvaluation_degreeCorankOneModelCoefficient]
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  refine Eq.trans ?_ ((h.measure.right_invariant k).integral_comp
    (rightTranslate (upperUnipotent (n + 1) F) k).measurableEmbedding _)
  congr 1
  funext t
  induction t using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk, sphericalQuotientDegree_mk, sphericalQuotientDegree_mk,
      exponent_mul_integral h.uniformizer g hk, corankOneIntegrand_mk, corankOneIntegrand_mk,
      inverseSphericalWhittaker_mul_integral h.conductor.1 h.uniformizer q x g hk,
      determinantWeight_mul_integral h.abv_unit g k hk, map_mul]
    rfl

/-- The action `g ↦ π(diag(g, 1))` of `GL_(n+1)` on the Whittaker model. -/
def restrictedModelRepresentation :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F) (coefficientModel π ℓ).toSubmodule :=
  (modelRepresentation π ℓ).comp (rankInclusion 1)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)] in
include hπ in
theorem restrictedModelRepresentation_isSmooth :
    IsSmooth (R := ℂ) (G := Langlands.GeneralLinear (n + 1) F)
      (V := (coefficientModel π ℓ).toSubmodule) (restrictedModelRepresentation π ℓ) := by
  intro w
  obtain ⟨K, hK⟩ := model_isSmooth π hπ ℓ w
  exact ⟨K.comap (rankInclusion 1) (rankInclusionContinuous 1).continuous,
    fun k => hK ⟨rankInclusion 1 k.val, k.property⟩⟩

/-- **Averaging.** Every model vector has a translate-average over
`diag(GL_(n+1)(O), 1)` that satisfies Jacquet's restriction-invariance clause and has
the same Laurent degree coefficients. -/
theorem exists_integralInvariant_degreeCoefficients_eq
    (w : (coefficientModel π ℓ).toSubmodule) :
    ∃ w' : (coefficientModel π ℓ).toSubmodule, IsIntegralInvariantOnRestriction π ℓ w' ∧
      ∀ d, degreeCorankOneModelCoefficient h π hπ ℓ w' d =
        degreeCorankOneModelCoefficient h π hπ ℓ w d := by
  have hρ := restrictedModelRepresentation_isSmooth π hπ ℓ
  have hK : IsCompact (levelOpenSubgroup F n 0 : Set (Langlands.GeneralLinear (n + 1) F)) :=
    isCompact_levelOpenSubgroup F n 0
  have hmem : ∀ k : levelOpenSubgroup F n 0,
      k.val ∈ integralSubgroup (ValuativeRel.valuation F).integer n := by
    intro k
    rw [← levelSubgroup_zero]
    exact k.property
  refine ⟨Compact.averageMap (V := (coefficientModel π ℓ).toSubmodule)
    (restrictedModelRepresentation π ℓ) hρ (levelOpenSubgroup F n 0) hK w, ?_, ?_⟩
  · intro g k
    have hk : k.val ∈ levelOpenSubgroup F n 0 := by
      change k.val ∈ levelSubgroup F n 0
      rw [levelSubgroup_zero]
      exact k.property
    have hfix := Compact.averageMap_mem_fixedVectors (V := (coefficientModel π ℓ).toSubmodule)
      (restrictedModelRepresentation π ℓ) hρ (levelOpenSubgroup F n 0) hK w ⟨k.val, hk⟩
    have hi := congrArg (fun z : (coefficientModel π ℓ).toSubmodule =>
      z.val.val (rankInclusion 1 g)) hfix
    change (Compact.averageMap (V := (coefficientModel π ℓ).toSubmodule)
        (restrictedModelRepresentation π ℓ) hρ (levelOpenSubgroup F n 0) hK w).val.val
          (rankInclusion 1 g * rankInclusion 1 k.val) =
      (Compact.averageMap (V := (coefficientModel π ℓ).toSubmodule)
        (restrictedModelRepresentation π ℓ) hρ (levelOpenSubgroup F n 0) hK w).val.val
          (rankInclusion 1 g) at hi
    simpa only [map_mul] using hi
  · intro d
    have := Compact.finite_orbit_of_smooth (V := (coefficientModel π ℓ).toSubmodule)
      (restrictedModelRepresentation π ℓ) hρ (levelOpenSubgroup F n 0) hK w
    have hres := linearMap_orbitMean_eq (E := (coefficientModel π ℓ).toSubmodule)
      ((restrictedModelRepresentation π ℓ).comp (levelOpenSubgroup F n 0).toSubgroup.subtype)
      (degreeCorankOneModelCoefficientLinearMap h π hπ ℓ d)
      (fun k u => degreeCorankOneModelCoefficient_integral_translate h π hπ ℓ k.val
        (hmem k) u d) w
    exact hres

/-- Equal Laurent degree coefficients give equal model denominator products. -/
theorem corankOneModelDenominatorProduct_eq_of_degreeCoefficients_eq
    (P : ℂ[X]) {w w' : (coefficientModel π ℓ).toSubmodule}
    (hd : ∀ d, degreeCorankOneModelCoefficient h π hπ ℓ w' d =
      degreeCorankOneModelCoefficient h π hπ ℓ w d) :
    corankOneModelDenominatorProduct h π hπ ℓ w' P =
      corankOneModelDenominatorProduct h π hπ ℓ w P := by
  unfold corankOneModelDenominatorProduct
  congr 1
  apply HahnSeries.ext
  funext d
  exact hd d

end Averaging

section Existence

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)

include hπ in
/-- **Existence of the essential vector from the JPSS inputs** (Jacquet 2012, Theorem 1,
existence part, sections 1-3). Let `P` be the standard L-polynomial of `π`. Suppose that
for every model vector `w` and every tuple of units `x`, the corank-one integral
`Ψ(s, w, W(x; ψ̄))` converges on a right half-plane and its product with
`∏ P(x_i q^(-s))` is `q^(-Ns) Q(q^(-s))` there for some `N` and polynomial `Q`; and that
for every `x` some finite family `w_j`, `e_j` satisfies
`(∑_j q^(-e_j s) Ψ(s, w_j, W(x; ψ̄))) ∏ P(x_i q^(-s)) = 1` on a right half-plane
(Jacquet's Lemma 4). Then the model of `ℓ` contains an essential vector. -/
theorem exists_isEssentialVector_of_jpss (P : ℂ[X])
    (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P)
    (hconv : ∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
      ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    (hpoly : ∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
      ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
        corankOneIntegral ψ abv μ w.val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s *
          (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
        spectralPoint q s ^ N * Q.eval (spectralPoint q s))
    (hgen : ∀ x : Fin (n + 1) → ℂˣ, ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule)
      (e : Fin k → ℤ) (a : ℝ), ∀ s : ℂ, a < s.re →
        (∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) *
          (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1) :
    ∃ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w := by
  have hfin : ∀ w, (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite :=
    fun w => corankOneModelDenominatorProduct_support_finite_of_jpss h π hπ ℓ P w
      (hconv w) (hpoly w)
  obtain ⟨w₀, hw₀, h1⟩ := exists_corankOneModelNumerator_eq_one h π hπ ℓ P (by
    intro x
    obtain ⟨k, W, e, hgx⟩ := hgen x
    have hsum := sum_numerator_evaluation_eq_one h π hπ ℓ P x W e (fun j => hfin (W j))
      (fun j => hconv (W j) x) hgx
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
    exact ⟨W j, hfin (W j), hj⟩)
  obtain ⟨w₁, hinv, hcoeff⟩ := exists_integralInvariant_degreeCoefficients_eq h π hπ ℓ w₀
  have hT := corankOneModelDenominatorProduct_eq_of_degreeCoefficients_eq h π hπ ℓ P hcoeff
  refine ⟨w₁, ⟨P, hP, fun x => ⟨hconv w₁ x, ?_⟩⟩, hinv⟩
  apply hasRationalContinuation_essentialFactor_of_coeff h π hπ ℓ P w₁ x (hconv w₁ x)
  intro d
  rw [hT]
  exact specializedDenominatorProduct_coeff_of_numerator_eq_one h π hπ ℓ P w₀ hw₀ h1 x d

end Existence

end Langlands.Conductor
