import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.RealStandardEllipticCartanNumerator

/-! # The elliptic numerator from a finite rotation Fourier window -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealStandardEllipticCartan

open RealBlockFourierFinite RealBlockPropagation

private def windowIndex (m : ℕ) : ℕ ↪ ℤ :=
  ⟨fun k => 2 * (k : ℤ) + 1 - (m : ℤ), by
    intro i j h
    change 2 * (i : ℤ) + 1 - (m : ℤ) = 2 * (j : ℤ) + 1 - (m : ℤ) at h
    omega⟩

private theorem window_eq_map_range (m : ℕ) :
    window m = (Finset.range m).map (windowIndex m) := by
  ext j
  rw [mem_window, abs_lt, Finset.mem_map]
  constructor
  · rintro ⟨⟨hj₁, hj₂⟩, ⟨a, ha⟩⟩
    have hapos : 1 ≤ a := by omega
    let k := (a - 1).toNat
    have hk : (k : ℤ) = a - 1 := Int.toNat_of_nonneg (by omega)
    refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    change 2 * (k : ℤ) + 1 - (m : ℤ) = j
    omega
  · rintro ⟨k, hk, rfl⟩
    have hkm := Finset.mem_range.mp hk
    change (-(m : ℤ) < 2 * (k : ℤ) + 1 - (m : ℤ) ∧
      2 * (k : ℤ) + 1 - (m : ℤ) < m) ∧
      Even (2 * (k : ℤ) + 1 - (m : ℤ) + m + 1)
    exact ⟨⟨by omega, by omega⟩, (k : ℤ) + 1, by omega⟩

/-- The average of the two sign contributions retains the required Fourier parity. -/
theorem signedLowSum_eq_windowSum (m : ℕ) (θ : ℝ) :
    (∑ j ∈ Finset.Ioo (-(m : ℤ)) (m : ℤ),
        ((1 + (-1 : ℂ) ^ (j + (m : ℤ) + 1)) / 2) * expMode j θ) =
      ∑ j ∈ window m, expMode j θ := by
  rw [window, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : Even (j + (m : ℤ) + 1)
  · rw [ite_eq_left h, h.neg_one_zpow]
    ring
  · rw [ite_eq_right h, (Int.not_even_iff_odd.mp h).neg_one_zpow]
    ring

/-- Multiplying the finite window sum by the angular Weyl factor leaves its two endpoint
exponentials. -/
theorem angularFactor_mul_windowSum (m : ℕ) (θ : ℝ) :
    (expMode 1 θ - expMode (-1) θ) * (∑ j ∈ window m, expMode j θ) =
      expMode (m : ℤ) θ - expMode (-(m : ℤ)) θ := by
  rw [window_eq_map_range, Finset.sum_map, sub_mul, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  let a (k : ℕ) := expMode (2 * (k : ℤ) - (m : ℤ)) θ
  have hmul (p q : ℤ) : expMode p θ * expMode q θ = expMode (p + q) θ :=
    congrFun (expMode_add p q) θ
  calc
    _ = ∑ k ∈ Finset.range m, (a (k + 1) - a k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      change expMode 1 θ * expMode (2 * (k : ℤ) + 1 - (m : ℤ)) θ -
        expMode (-1) θ * expMode (2 * (k : ℤ) + 1 - (m : ℤ)) θ = _
      rw [hmul, hmul]
      unfold a
      congr 2 <;> omega
    _ = a m - a 0 := Finset.sum_range_sub a m
    _ = _ := by
      unfold a
      congr 2 <;> omega

private theorem complexTerm_eq_radial_mul_expMode (m : ℤ) (t : ℂ) (x θ : ℝ) :
    complexTerm (m, t) (Multiplicative.ofAdd (x, θ)) =
      Complex.exp ((x : ℂ) * (2 * t)) * expMode m θ := by
  change Complex.exp ((x : ℂ) * (2 * t) + (θ : ℂ) * (Complex.I * (m : ℂ))) = _
  rw [Complex.exp_add, expMode]
  congr 2
  ring

/-- The radial twist of the finite window gives the complex-slot term of the Cartan
numerator after multiplication by the angular Weyl factor. -/
def RealStandardEllipticCartanWindowStatement : Prop :=
  ∀ (m : ℕ) (t : ℂ) (x θ : ℝ),
    (expMode 1 θ - expMode (-1) θ) *
        (Complex.exp ((x : ℂ) * (2 * t)) * ∑ j ∈ window m, expMode j θ) =
      complexTerm (m, t) (Multiplicative.ofAdd (x, θ)) -
        complexTerm (-(m : ℤ), t) (Multiplicative.ofAdd (x, θ))

theorem realStandardEllipticCartanWindow : RealStandardEllipticCartanWindowStatement := by
  intro m t x θ
  rw [mul_left_comm, angularFactor_mul_windowSum, complexTerm_eq_radial_mul_expMode,
    complexTerm_eq_radial_mul_expMode, mul_sub]

end Langlands.Archimedean.RealStandardEllipticCartan
