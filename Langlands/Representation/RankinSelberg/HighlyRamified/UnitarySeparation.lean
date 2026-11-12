import Langlands.Representation.Conductor.EssentialRestrictionUniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Separation by unitary Satake parameters

A Laurent polynomial over `ℂ` vanishing at every tuple of complex numbers of absolute
value `1` is zero, since the unit circle is infinite. Consequently the separation theorem
for corank-one integrals of a restriction-invariant model vector needs the vanishing of
the integrals against the spherical functions only for unitary Satake parameters.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory Filter Topology MvPolynomial
open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration Langlands.Conductor

universe uF uV uσ

section Laurent

/-- The unit circle of `ℂ` is infinite. -/
theorem unitCircle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  have hinj : Set.InjOn (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) (Set.Icc 0 1) :=
    Circle.coe_injective.comp_injOn (Circle.exp_injOn_Icc (by linarith [Real.two_le_pi]))
  refine Set.Infinite.mono ?_ ((Set.Icc_infinite zero_lt_one).image hinj)
  rintro _ ⟨θ, -, rfl⟩
  exact Circle.norm_coe _

variable (σ : Type uσ) [Fintype σ]

/-- Evaluations at unitary tuples separate Laurent polynomials over `ℂ`. -/
theorem torusPolynomial_eq_zero_of_unit_evaluations
    (p : TorusPolynomialAlgebra σ ℂ)
    (hp : ∀ x : σ → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) →
      torusPolynomialEvaluation σ ℂ x p = 0) : p = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (∏ i : σ, (X i : MvPolynomial σ ℂ)) p
  have hazero : a = 0 := by
    apply MvPolynomial.funext_set (fun _ : σ => {z : ℂ | ‖z‖ = 1})
      (fun _ => unitCircle_infinite)
    intro x hx
    have hx1 : ∀ i, ‖x i‖ = 1 := fun i => hx i (Set.mem_univ i)
    have hx0 : ∀ i, x i ≠ 0 := fun i h0 => by
      have := hx1 i
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    let xu : σ → ℂˣ := fun i => Units.mk0 (x i) (hx0 i)
    have he := congrArg (torusPolynomialEvaluation σ ℂ xu) ha
    rw [map_mul, hp xu hx1, zero_mul, torusPolynomialEvaluation_algebraMap] at he
    change (0 : ℂ) = MvPolynomial.eval x a at he
    simpa only [map_zero] using he.symm
  rw [hazero, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit
    (S := TorusPolynomialAlgebra σ ℂ) (∏ i : σ, (X i : MvPolynomial σ ℂ))).pow m
      ).mul_right_cancel (by simpa only [zero_mul] using ha)

/-- Evaluations at unitary tuples separate symmetric Laurent polynomials over `ℂ`. -/
theorem symmetricTorus_eq_zero_of_unit_evaluations
    (p : symmetricTorusSubalgebra σ ℂ)
    (hp : ∀ x : σ → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) →
      symmetricTorusEvaluation σ ℂ x p = 0) : p = 0 :=
  Subtype.ext (torusPolynomial_eq_zero_of_unit_evaluations σ p.val hp)

end Laurent

section Bridge

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

/-- If, for every unitary Satake parameter `x`, the corank-one integrals of a smooth
model vector converge and vanish on a real half-line, then every Laurent degree
coefficient vanishes. -/
theorem degreeCorankOneModelCoefficient_eq_zero_of_unit_integrals_eq_zero
    (hzero : ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) → ∃ a : ℝ, ∀ s : ℝ, a < s →
      CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s = 0)
    (d : ℤ) : degreeCorankOneModelCoefficient h π hπ ℓ w d = 0 := by
  apply symmetricTorus_eq_zero_of_unit_evaluations
  intro x hx
  obtain ⟨d₀, hd₀⟩ := degreeCorankOneModelCoefficient_eq_zero_below h π hπ ℓ w
  obtain ⟨a, ha⟩ := hzero x hx
  have hq1 : (1 : ℝ) < q := by exact_mod_cast h.one_lt_q
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hcbelow : ∀ e < d₀, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelCoefficient h π hπ ℓ w e) = 0 := fun e he => by
    rw [hd₀ e he, map_zero]
  refine eq_zero_of_hasSum_int_eq_zero hcbelow (Real.rpow_pos_of_pos hq0 (-a)) ?_ d
  intro X hX hXr
  set s : ℝ := -Real.log X / Real.log q with hsdef
  have hs : a < s := by
    have h1 : Real.log X < Real.log ((q : ℝ) ^ (-a)) := Real.log_lt_log hX hXr
    rw [Real.log_rpow hq0] at h1
    rw [hsdef, lt_div_iff₀ hlogq]
    linarith
  have hrpow : (q : ℝ) ^ (-s) = X := by
    rw [Real.rpow_def_of_pos hq0]
    have hl : Real.log q ≠ 0 := hlogq.ne'
    have hm : Real.log q * -s = Real.log X := by
      rw [hsdef]
      field_simp
    rw [hm, Real.exp_log hX]
  have hXs : spectralPoint q (s : ℂ) = (X : ℂ) := by
    rw [spectralPoint_ofReal, hrpow]
  obtain ⟨hconv, hint⟩ := ha s hs
  have hsum := hasSum_corankOneIntegral h w.val _ (s : ℂ) hconv
  rw [hint, hXs] at hsum
  convert hsum using 1
  funext e
  rw [mul_comm, symmetricTorusEvaluation_degreeCorankOneModelCoefficient]

include hπ in
/-- Under the same hypothesis, a restriction-invariant smooth model vector vanishes on
`diag(GL_(n+1), 1)`. -/
theorem eq_zero_on_restriction_of_unit_integrals_eq_zero
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hzero : ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) → ∃ a : ℝ, ∀ s : ℝ, a < s →
      CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s = 0)
    (g : Langlands.GeneralLinear (n + 1) F) :
    w.val.val (rankInclusion 1 g) = 0 :=
  eq_zero_on_restriction_of_degreeCoefficients_eq_zero h π hπ ℓ w hw
    (degreeCorankOneModelCoefficient_eq_zero_of_unit_integrals_eq_zero h π hπ ℓ w hzero) g

include hπ in
/-- Under the same hypothesis, a restriction-invariant smooth model vector vanishes on the
mirabolic subgroup. -/
theorem eq_zero_on_mirabolic_of_unit_integrals_eq_zero
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hzero : ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) → ∃ a : ℝ, ∀ s : ℝ, a < s →
      CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s = 0)
    (p : mirabolic (n + 1) F) :
    w.val.val p.val = 0 := by
  have h0 := whittaker_mirabolic_eq_of_levi_eq ψ w.val 0
    (fun g => (eq_zero_on_restriction_of_unit_integrals_eq_zero h π hπ ℓ w hw hzero g).trans
      rfl) p
  exact h0

end Bridge

end Langlands.RankinSelberg.HighlyRamified
