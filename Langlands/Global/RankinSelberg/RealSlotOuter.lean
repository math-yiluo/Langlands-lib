import Langlands.Global.RankinSelberg.RealSlotLevi
import Langlands.Representation.Archimedean.RealLeviTwoBlock

/-! # The spherical majorant on the opposite radical chart -/

noncomputable section

open MeasureTheory Matrix
open Langlands.Archimedean
open Langlands.Archimedean.RealLeviChartIntegrable

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

variable {N : ℕ}

/-! ## The spherical function -/

/-- The spherical function `g ↦ exp(Σ_i c_i α_i(g))` in the Iwasawa coordinates. -/
def spherical (c : Fin N → ℝ) (g : Langlands.GeneralLinear N ℝ) : ℝ :=
  Real.exp (∑ i, c i * RealIwasawa.alpha g i)

theorem spherical_pos (c : Fin N → ℝ) (g : Langlands.GeneralLinear N ℝ) : 0 < spherical c g :=
  Real.exp_pos _

theorem spherical_mul_unitary (c : Fin N → ℝ) (g : Langlands.GeneralLinear N ℝ)
    (k : unitaryCompact ℝ N) : spherical c (g * (k : Langlands.GeneralLinear N ℝ)) = spherical c g := by
  rw [spherical, RealIwasawa.alpha_mul_unitary, spherical]

theorem spherical_torus_mul (c y : Fin N → ℝ) (g : Langlands.GeneralLinear N ℝ) :
    spherical c (RealIwasawa.torus y * g) = Real.exp (∑ i, c i * y i) * spherical c g := by
  rw [spherical, RealIwasawa.alpha_torus_mul, spherical, ← Real.exp_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem continuous_spherical (c : Fin N → ℝ) : Continuous (spherical c) :=
  Real.continuous_exp.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp RealIwasawa.continuous_alpha))

/-! ## Gram determinants in Iwasawa coordinates -/

theorem mul_transpose_of_mem (k : unitaryCompact ℝ N) :
    ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) *
      ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)ᵀ = 1 := by
  have h := k.property
  change ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) ∈
    Matrix.unitaryGroup (Fin N) ℝ at h
  rw [Matrix.mem_unitaryGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- The Gram determinant of the rows `l, …, N - 1` is `exp(2 Σ_{i ≥ l} α_i)`. -/
theorem gram_eq_exp_alpha (g : Langlands.GeneralLinear N ℝ) (l : ℕ) :
    GramFormula.gram l (g : Matrix (Fin N) (Fin N) ℝ) =
      Real.exp (2 * ∑ i : Fin N, if l ≤ (i : ℕ) then RealIwasawa.alpha g i else 0) := by
  have hg : (g : Matrix (Fin N) (Fin N) ℝ) =
      ((RealIwasawa.bpart g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) *
        ((RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) := by
    rw [← Units.val_mul, RealIwasawa.bpart_mul_kpart]
  rw [hg, GramFormula.gram_mul (RealIwasawa.isPosUpper_bpart g).1
    (mul_transpose_of_mem (RealIwasawa.kpart g)), GramFormula.diagonalTail]
  rw [show (2 : ℝ) * ∑ i : Fin N, (if l ≤ (i : ℕ) then RealIwasawa.alpha g i else 0) =
    ∑ i : Fin N, ((if l ≤ (i : ℕ) then RealIwasawa.alpha g i else 0) +
      (if l ≤ (i : ℕ) then RealIwasawa.alpha g i else 0)) by
      rw [Finset.sum_add_distrib]; ring]
  rw [Real.exp_sum, sq, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rw [Real.exp_add, RealIwasawa.exp_alpha]
  · simp

/-- The Gram exponents attached to a spherical exponent `c`. -/
def gramExponent (c : Fin N → ℝ) (l : Fin N) : ℝ :=
  if h : (l : ℕ) = 0 then c l / 2 else (c l - c ⟨l - 1, by omega⟩) / 2

theorem sum_gramExponent (c : Fin N → ℝ) (i : Fin N) :
    ∑ l : Fin N, (if (l : ℕ) ≤ i then 2 * gramExponent c l else 0) = c i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero =>
    rw [Finset.sum_eq_single (⟨0, hi⟩ : Fin N)]
    · simp only [gramExponent, le_refl, ite_true, dite_true]
      ring
    · intro l _ hl
      have : ¬ (l : ℕ) ≤ 0 := fun h => hl (Fin.ext (by simpa using h))
      simp [this]
    · simp
  | succ i ih =>
    have ih' := ih (by omega)
    have hsplit : ∀ l : Fin N, (if (l : ℕ) ≤ i + 1 then 2 * gramExponent c l else 0) =
        (if (l : ℕ) ≤ i then 2 * gramExponent c l else 0) +
          (if l = (⟨i + 1, hi⟩ : Fin N) then 2 * gramExponent c l else 0) := by
      intro l
      by_cases h1 : (l : ℕ) ≤ i
      · have h2 : l ≠ ⟨i + 1, hi⟩ := fun e => by rw [e] at h1; simp at h1
        simp [h1, h2, show (l : ℕ) ≤ i + 1 by omega]
      · by_cases h2 : l = ⟨i + 1, hi⟩
        · subst h2; simp
        · have h3 : ¬ (l : ℕ) ≤ i + 1 := fun h => h2 (Fin.ext (by simp; omega))
          simp [h1, h2, h3]
    rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib, ih']
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, gramExponent]
    simp only [show (i + 1 : ℕ) ≠ 0 by omega, dite_false, Nat.add_sub_cancel]
    ring

/-- **The spherical function as a product of Gram determinants.** -/
theorem spherical_eq_prod_gram (c : Fin N → ℝ) (g : Langlands.GeneralLinear N ℝ) :
    spherical c g = ∏ l : Fin N,
      GramFormula.gram (l : ℕ) (g : Matrix (Fin N) (Fin N) ℝ) ^ gramExponent c l := by
  simp_rw [gram_eq_exp_alpha, ← Real.exp_mul, ← Real.exp_sum]
  rw [spherical]
  congr 1
  have h : ∀ l : Fin N, 2 * (∑ i : Fin N, if (l : ℕ) ≤ (i : ℕ) then RealIwasawa.alpha g i else 0) *
      gramExponent c l = ∑ i : Fin N,
        (if (l : ℕ) ≤ (i : ℕ) then 2 * gramExponent c l else 0) * RealIwasawa.alpha g i := by
    intro l
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, sum_gramExponent]

/-! ## The opposite radical chart -/

section Chart

variable {μ : Fin N → ℕ} (hμ : Monotone μ)
include hμ

/-- **Integrability of the spherical function on the chart.** If the exponents `c` decrease
by at least one at every step, and by more than one when the block index increases, then the
spherical function is integrable on the opposite radical chart. -/
theorem integrable_spherical_lowerCGL (c : Fin N → ℝ)
    (h1 : ∀ (k l : Fin N), (k : ℕ) + 1 = l → c l ≤ c k - 1)
    (h2 : ∀ (k l : Fin N), (k : ℕ) + 1 = l → μ k < μ l → c l < c k - 1) :
    Integrable fun X : CoordC μ → ℝ => spherical c (RealLeviTwoBlock.lowerCGL hμ X) := by
  let γ : ℕ → ℝ := fun l => if h : l < N then gramExponent c ⟨l, h⟩ else 0
  have hγ : ∀ l : Fin N, γ l = gramExponent c l := fun l => by simp [γ, l.isLt]
  have hstep : ∀ (k l : Fin N), (k : ℕ) + 1 = l → gramExponent c l = (c l - c k) / 2 := by
    intro k l hkl
    have hk : k = ⟨(l : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
    simp only [gramExponent, show (l : ℕ) ≠ 0 by omega, dite_false, hk]
  have hfin := gen N μ hμ γ (fun l hl => by
      rw [hγ]
      have hk : ((⟨(l : ℕ) - 1, by omega⟩ : Fin N) : ℕ) + 1 = l := by simp; omega
      rw [hstep _ l hk]
      have := h1 _ l hk
      linarith)
    (fun k l hkl hlt => by
      rw [hγ, hstep k l hkl]
      have := h2 k l hkl hlt
      linarith)
  simp only [hγ] at hfin
  have hpos : ∀ X : CoordC μ → ℝ, 0 ≤ ∏ l : Fin N,
      GramFormula.gram (l : ℕ) (lowerC μ X) ^ gramExponent c l :=
    fun X => Finset.prod_nonneg fun l _ => Real.rpow_nonneg (gram_lowerC_pos hμ X l).le _
  have heq : (fun X : CoordC μ → ℝ => spherical c (RealLeviTwoBlock.lowerCGL hμ X)) =
      fun X => ∏ l : Fin N, GramFormula.gram (l : ℕ) (lowerC μ X) ^ gramExponent c l := by
    funext X
    rw [spherical_eq_prod_gram, RealLeviTwoBlock.lowerCGL_val]
  rw [heq]
  refine ⟨(continuous_prod_gram hμ _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
  exact hfin

end Chart

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
