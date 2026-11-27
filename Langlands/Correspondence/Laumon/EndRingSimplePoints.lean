import Langlands.Correspondence.Laumon.EndRingDvr

/-!
# Simple points of the end ring

A *simple point* of `endRing k` is an element `b` which is a root of a polynomial `G` over `k[x]`
whose derivative at `b` is a unit (`IsSimplePoint`). This module shows that every element of
`endRing k` separable over `k(t)` lies in the field generated over `k(t)` by a simple point
(`exists_isSimplePoint`).
-/

noncomputable section

universe u

open Polynomial IsLocalRing

namespace Langlands.Henniart.Laumon

variable (k : Type u) [Field k]

local notation "ι" => endChartCoordinate k FourierEnd.zero
local notation "τ" => endUniformizer k FourierEnd.zero

theorem endResidue_endUniformizer (e : FourierEnd) : endResidue k (endUniformizer k e) = 0 := by
  rw [endResidue_apply, endPowerSeriesHom_endUniformizer, PowerSeries.constantCoeff_X]

theorem endResidue_endChartCoordinate (e : FourierEnd) (a : k[X]) :
    endResidue k (endChartCoordinate k e a) = a.coeff 0 := by
  rw [endResidue_apply, endPowerSeriesHom_endChartCoordinate,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]

theorem isUnit_iff_endResidue_ne_zero (x : endRing k) : IsUnit x ↔ endResidue k x ≠ 0 :=
  isUnit_endRing_iff k x

theorem endUniformizer_ne_zero (e : FourierEnd) : endUniformizer k e ≠ 0 :=
  (irreducible_endUniformizer k e).ne_zero

/-- The chart coordinate, followed by the inclusion into the end field, is the expansion
`k[x] → k(x) → endField k`. -/
theorem subtype_comp_endChartCoordinate (e : FourierEnd) :
    (endRing k).subtype.comp (endChartCoordinate k e) =
      (algebraMap (RatFunc k) (endField k)).comp (algebraMap k[X] (RatFunc k)) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, endChartCoordinate, coe_eval₂RingHom, eval₂_C,
      RatFunc.algebraMap_C]
    rfl
  · simp only [RingHom.comp_apply, endChartCoordinate, coe_eval₂RingHom, eval₂_X,
      RatFunc.algebraMap_X]
    rfl

theorem coe_endChartCoordinate (e : FourierEnd) (a : k[X]) :
    ((endChartCoordinate k e a : endRing k) : endField k) =
      algebraMap (RatFunc k) (endField k) (algebraMap k[X] (RatFunc k) a) :=
  RingHom.congr_fun (subtype_comp_endChartCoordinate k e) a

theorem coe_endUniformizer (e : FourierEnd) :
    ((endUniformizer k e : endRing k) : endField k) =
      algebraMap (RatFunc k) (endField k) RatFunc.X := rfl

/-- Evaluating a polynomial over `k[x]` at an element of the end ring, inside the end field. -/
theorem coe_eval₂_endChartCoordinate (p : k[X][X]) (b : endRing k) :
    ((eval₂ ι b p : endRing k) : endField k) =
      aeval (b : endField k) (p.map (algebraMap k[X] (RatFunc k))) := by
  rw [aeval_def, eval₂_map]
  change (endRing k).subtype (eval₂ ι b p) = _
  rw [hom_eval₂, subtype_comp_endChartCoordinate]
  rfl

/-- If the image of a polynomial `a ∈ k[x]` in the end ring is divisible by `t ^ n`, then `a` is
divisible by `x ^ n`. -/
theorem X_pow_dvd_of_endChartCoordinate_eq (a : k[X]) (n : ℕ) (r : endRing k)
    (h : ι a = τ ^ n * r) : X ^ n ∣ a := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have h' := congrArg (endPowerSeriesHom k) h
  rw [endPowerSeriesHom_endChartCoordinate, map_mul, map_pow,
    endPowerSeriesHom_endUniformizer] at h'
  have hdvd : (PowerSeries.X : PowerSeries k) ^ n ∣ (a : PowerSeries k) := ⟨_, h'⟩
  rw [PowerSeries.X_pow_dvd_iff] at hdvd
  have := hdvd d hd
  rwa [Polynomial.coeff_coe] at this

/-- Every element of the end field becomes an element of the end ring after multiplication by a
power of `t`. -/
theorem exists_pow_mul_mem_endRing (z : endField k) :
    ∃ M : ℕ, ((τ : endRing k) : endField k) ^ M * z ∈ endRing k := by
  obtain ⟨w, hw⟩ : ∃ w : LaurentSeries k, w = (z : LaurentSeries k) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = (-w.order).toNat := ⟨_, rfl⟩
  refine ⟨M, PowerSeries.X ^ ((M : ℤ) + w.order).toNat * w.powerSeriesPart, ?_⟩
  have hτ : (((τ : endRing k) : endField k) : LaurentSeries k) =
      HahnSeries.ofPowerSeries ℤ k PowerSeries.X := by
    rw [← ofPowerSeries_endPowerSeriesHom, endPowerSeriesHom_endUniformizer]
  have hnn : 0 ≤ (M : ℤ) + w.order := by omega
  change _ = ((((τ : endRing k) : endField k) ^ M * z : endField k) : LaurentSeries k)
  rw [IntermediateField.coe_mul, IntermediateField.coe_pow, hτ, ← hw, map_mul, ← map_pow,
    HahnSeries.ofPowerSeries_X_pow, HahnSeries.ofPowerSeries_X_pow, Int.toNat_of_nonneg hnn]
  have key := LaurentSeries.single_order_mul_powerSeriesPart w
  conv_rhs => rw [← key]
  rw [← mul_assoc, HahnSeries.single_mul_single, one_mul]

/-- A *simple point* of the end ring: a root `b` of a polynomial `G` over `k[x]` such that
`G'(b)` is a unit. -/
def IsSimplePoint (b : endRing k) : Prop :=
  ∃ G : k[X][X], eval₂ ι b G = 0 ∧ IsUnit (eval₂ ι b (derivative G))

/-- A root `b` of `u₀ + u₁ Y + x K₀ Y ^ 2` with `u₁(b)` a unit is a simple point. -/
theorem isSimplePoint_of_eq (b v : endRing k) (u₀ u₁ : k[X]) (K₀ : k[X][X]) (hv : IsUnit v)
    (h₀ : ι u₀ = -(v * b + τ * eval₂ ι b K₀ * b ^ 2)) (h₁ : ι u₁ = v) : IsSimplePoint k b := by
  have hιX : ι X = τ := eval₂_X _ _
  refine ⟨C u₀ + C u₁ * X + C (X : k[X]) * K₀ * X ^ 2, ?_, ?_⟩
  · rw [eval₂_add, eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, eval₂_C, eval₂_X,
      eval₂_X_pow, h₀, h₁, hιX]
    ring
  · have hder : derivative (C u₀ + C u₁ * X + C (X : k[X]) * K₀ * X ^ 2) =
        C u₁ + C (X : k[X]) * derivative (K₀ * X ^ 2) := by
      simp only [derivative_add, derivative_C, mul_assoc, derivative_C_mul, derivative_X, mul_one,
        zero_add]
    rw [hder, eval₂_add, eval₂_mul, eval₂_C, eval₂_C, h₁, hιX, isUnit_iff_endResidue_ne_zero,
      RingHom.map_add, RingHom.map_mul, endResidue_endUniformizer, zero_mul, add_zero,
      ← isUnit_iff_endResidue_ne_zero]
    exact hv

/-- **Simple points.** Every element `γ` of the end ring separable over `k(t)` lies in the field
generated over `k(t)` by a simple point. If `m` is a polynomial over `k[x]` with `m(γ) = 0` and
`m'(γ) = t ^ δ v`, `v` a unit, then `b = (γ - γ_N) / t ^ N` with `N = δ + 1` and `γ_N` the
truncation of `γ` below degree `N` is a root of `m(γ_N + x ^ N Y) / x ^ (N + δ)`, whose
derivative at `b` is a unit. -/
theorem exists_isSimplePoint (γ : endRing k) (hγ : IsSeparable (RatFunc k) (γ : endField k)) :
    ∃ b : endRing k, IsSimplePoint k b ∧
      (γ : endField k) ∈ IntermediateField.adjoin (RatFunc k) {(b : endField k)} := by
  classical
  -- a polynomial over `k[x]` with simple root `γ`
  obtain ⟨m, hm0, hm1⟩ : ∃ m : k[X][X], eval₂ ι γ m = 0 ∧ eval₂ ι γ (derivative m) ≠ 0 := by
    obtain ⟨d, hd, hdm⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors k[X])
      (minpoly (RatFunc k) (γ : endField k))
    have hd0 : algebraMap k[X] (RatFunc k) d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2
        (nonZeroDivisors.ne_zero hd)
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors k[X])
      (minpoly (RatFunc k) (γ : endField k)), ?_, ?_⟩
    · apply Subtype.ext
      rw [coe_eval₂_endChartCoordinate, hdm, Algebra.smul_def, map_mul, minpoly.aeval, mul_zero]
      rfl
    · intro h
      have h' := congrArg (fun z : endRing k => (z : endField k)) h
      rw [coe_eval₂_endChartCoordinate, ← derivative_map, hdm, derivative_smul, Algebra.smul_def,
        map_mul, Polynomial.algebraMap_apply, aeval_C] at h'
      exact mul_ne_zero ((_root_.map_ne_zero _).2 hd0)
        (Polynomial.Separable.aeval_derivative_ne_zero hγ (minpoly.aeval _ _))
        (h'.trans (ZeroMemClass.coe_zero _))
  obtain ⟨δ, v, hv, hδ⟩ := exists_eq_endUniformizer_pow_mul k .zero _ hm1
  obtain ⟨γN, hγN⟩ : ∃ q : k[X], q = PowerSeries.trunc (δ + 1) (endPowerSeriesHom k γ) :=
    ⟨_, rfl⟩
  have hdvd : τ ^ (δ + 1) ∣ γ - ι γN := by
    rw [endRing_dvd_iff, map_pow, endPowerSeriesHom_endUniformizer, RingHom.map_sub,
      endPowerSeriesHom_endChartCoordinate, PowerSeries.X_pow_dvd_iff]
    intro i hi
    rw [map_sub, Polynomial.coeff_coe, hγN, PowerSeries.coeff_trunc]
    simp [hi]
  obtain ⟨b, hb⟩ := hdvd
  have hγb : γ = ι γN + τ ^ (δ + 1) * b := by rw [← hb]; ring
  refine ⟨b, ?_, ?_⟩
  swap
  · have hc : (γ : endField k) = ((ι γN : endRing k) : endField k) +
        ((τ : endRing k) : endField k) ^ (δ + 1) * (b : endField k) := by
      simp only [hγb, Subring.coe_add, Subring.coe_mul, Subring.coe_pow]
    rw [hc, coe_endChartCoordinate, coe_endUniformizer]
    exact add_mem (IntermediateField.algebraMap_mem _ _)
      (mul_mem (pow_mem (IntermediateField.algebraMap_mem _ _) _)
        (IntermediateField.mem_adjoin_simple_self _ _))
  -- the expansion of `m (γ_N + x ^ N Y)`
  obtain ⟨K₀, hK₀⟩ := binomExpansion (m.map (C : k[X] →+* k[X][X])) (C γN)
    (C ((X : k[X]) ^ (δ + 1)) * X)
  obtain ⟨e, he⟩ : ∃ e : k[X][X] →+* endRing k, e = eval₂RingHom ι b := ⟨_, rfl⟩
  have heC (a : k[X]) : e (C a) = ι a := by rw [he]; exact eval₂_C _ _
  have heX : e X = b := by rw [he]; exact eval₂_X _ _
  have hcomp : e.comp C = ι := RingHom.ext fun a => heC a
  have hιX : ι X = τ := eval₂_X _ _
  have hZ : e (C γN + C ((X : k[X]) ^ (δ + 1)) * X) = γ := by
    rw [map_add, map_mul, heC, heC, heX, map_pow, hιX, ← hγb]
  have hE : ι (m.eval γN) + ι ((derivative m).eval γN) * (τ ^ (δ + 1) * b) +
      e K₀ * (τ ^ (δ + 1) * b) ^ 2 = 0 := by
    have h := congrArg e hK₀
    rw [eval_map_apply, derivative_map, eval_map_apply, eval_map, hom_eval₂, hcomp, hZ, hm0] at h
    simp only [map_add, map_mul, map_pow, heC, heX, hιX] at h
    exact h.symm
  -- the derivative coefficient is `t ^ δ` times a unit
  obtain ⟨c, hc⟩ := sub_dvd_eval_sub γ (ι γN) ((derivative m).map ι)
  rw [eval_map, eval_map_apply, hδ, hb] at hc
  obtain ⟨v', hv'⟩ : ∃ v' : endRing k, v' = v - τ * b * c := ⟨_, rfl⟩
  have hu₁ : ι ((derivative m).eval γN) = τ ^ δ * v' := by
    rw [hv']
    linear_combination -hc
  have hv'u : IsUnit v' := by
    rw [isUnit_iff_endResidue_ne_zero, hv', RingHom.map_sub, map_mul, map_mul,
      endResidue_endUniformizer, zero_mul, zero_mul, sub_zero,
      ← isUnit_iff_endResidue_ne_zero]
    exact hv
  obtain ⟨u₁, hu₁'⟩ := X_pow_dvd_of_endChartCoordinate_eq k _ δ v' hu₁
  have hιu₁ : ι u₁ = v' := by
    rw [hu₁', map_mul, map_pow, hιX] at hu₁
    exact mul_left_cancel₀ (pow_ne_zero _ (endUniformizer_ne_zero k _)) hu₁
  -- the constant coefficient is divisible by `t ^ (N + δ)`
  have hu₀ : ι (m.eval γN) = τ ^ (δ + 1 + δ) * (-(v' * b + τ * e K₀ * b ^ 2)) := by
    rw [hu₁] at hE
    linear_combination hE
  obtain ⟨u₀, hu₀'⟩ := X_pow_dvd_of_endChartCoordinate_eq k _ _ _ hu₀
  have hιu₀ : ι u₀ = -(v' * b + τ * e K₀ * b ^ 2) := by
    rw [hu₀', map_mul, map_pow, hιX] at hu₀
    exact mul_left_cancel₀ (pow_ne_zero _ (endUniformizer_ne_zero k _)) hu₀
  rw [he] at hιu₀
  exact isSimplePoint_of_eq k b v' u₀ u₁ K₀ hv'u hιu₀ hιu₁

end Langlands.Henniart.Laumon
