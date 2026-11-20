import Langlands.Representation.Archimedean.RealLeviCompactChart
import Mathlib.MeasureTheory.Integral.PeakFunction

/-! # Compact tests peaked at the identity in lower matrix coordinates -/

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped Matrix.Norms.Operator Topology

namespace Langlands.Archimedean.RealCartanPeakTest

open RealLeviCompactChart RealCartanFixedFlag OrthogonalFinitePolynomial

set_option autoImplicit false

local notation "Mat" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ

/-- The positions strictly below the diagonal. -/
abbrev LowerIndex (n : ℕ) := {ij : Fin n × Fin n // ij.2 < ij.1}

/-- Projection to the strictly lower matrix entries. -/
def lowerProjection (n : ℕ) : Mat n →L[ℝ] (LowerIndex n → ℝ) :=
  ({ toFun := fun A ij => A ij.1.1 ij.1.2
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Mat n →ₗ[ℝ] (LowerIndex n → ℝ)).toContinuousLinearMap

@[simp]
theorem lowerProjection_apply {n : ℕ} (A : Mat n) (ij : LowerIndex n) :
    lowerProjection n A ij = A ij.1.1 ij.1.2 := rfl

@[simp]
theorem lowerProjection_one (n : ℕ) : lowerProjection n 1 = 0 := by
  funext ij
  exact Matrix.one_apply_ne (ne_of_gt ij.2)

private theorem eq_one_of_lowerProjection_eq_zero {n : ℕ} {k : K n}
    (hL : lowerProjection n (k : Mat n) = 0) (hD : ∀ i, 0 ≤ (k : Mat n) i i) :
    k = 1 := by
  let A : Mat n := k
  have hA : A * Aᵀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff.mp k.2)
  have hnormal : A * Aᵀ = Aᵀ * A := hA.trans (mul_eq_one_comm.mp hA).symm
  have hupper : A.IsUpperTriangular := fun i j hij =>
    congrFun hL ⟨(i, j), hij⟩
  have hoff {i j : Fin n} (hij : i ≠ j) : A i j = 0 :=
    eq_zero_of_block_ne_of_normal hnormal hupper hij
  have hdiag (i : Fin n) : A i i = 1 := by
    have he := congrArg (fun B : Mat n => B i i) hA
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, ← pow_two] at he
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hoff hj.symm, zero_pow (by decide)])
      (fun hn => (hn (Finset.mem_univ i)).elim)] at he
    have hprod : (A i i - 1) * (A i i + 1) = 0 := by nlinarith only [he]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have hn := hD i
      change 0 ≤ A i i at hn
      linarith
  apply Subtype.ext
  ext i j
  by_cases h : i = j
  · subst j
    change A i i = (1 : Mat n) i i
    rw [hdiag, Matrix.one_apply_eq]
  · exact (hoff h).trans (Matrix.one_apply_ne h).symm

/-- The diagonal cutoff removes the other diagonal sign matrices from
the zero set of the projected coordinates. -/
def diagonalCutoff {n : ℕ} (k : K n) : ℝ :=
  ∏ i : Fin n, max 0 ((k : Mat n) i i)

theorem continuous_diagonalCutoff (n : ℕ) : Continuous (diagonalCutoff : K n → ℝ) :=
  continuous_finsetProd _ fun i _ => continuous_const.max (continuous_subtype_val.matrix_elem i i)

@[simp]
theorem diagonalCutoff_one (n : ℕ) : diagonalCutoff (1 : K n) = 1 := by
  simp [diagonalCutoff]

/-- The unnormalized test is a ball peak on the lower entries times the
diagonal cutoff. -/
def rawTest (n : ℕ) (ε : ℝ) : C(K n, ℝ) where
  toFun k := diagonalCutoff k * max 0 (ε - ‖lowerProjection n (k : Mat n)‖)
  continuous_toFun := (continuous_diagonalCutoff n).mul
    (continuous_const.max (continuous_const.sub ((lowerProjection n).continuous.comp
      continuous_subtype_val).norm))

theorem rawTest_nonneg (n : ℕ) (ε : ℝ) (k : K n) : 0 ≤ rawTest n ε k :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => le_max_left _ _) (le_max_left _ _)

theorem rawTest_mass_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ k, rawTest n ε k ∂compactHaar n := by
  apply (rawTest n ε).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := compactHaar n) (x := 1)
    (HasCompactSupport.of_compactSpace _) (rawTest_nonneg n ε)
  change diagonalCutoff (1 : K n) * max 0 (ε - ‖lowerProjection n 1‖) ≠ 0
  simp [hε.le, hε.ne']

theorem eventually_support_rawTest_subset (n : ℕ) {U : Set (K n)}
    (hU : IsOpen U) (hOne : 1 ∈ U) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.support (rawTest n ε) ⊆ U := by
  let bad : Set (K n) := Uᶜ ∩ ⋂ i : Fin n, {k | 0 ≤ (k : Mat n) i i}
  let L : K n → (LowerIndex n → ℝ) := fun k => lowerProjection n (k : Mat n)
  have hbad : IsClosed bad :=
    hU.isClosed_compl.inter (isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_subtype_val.matrix_elem i i))
  have hclosed : IsClosed (L '' bad) :=
    (hbad.isCompact.image ((lowerProjection n).continuous.comp continuous_subtype_val)).isClosed
  have h0 : 0 ∉ L '' bad := by
    rintro ⟨k, hk, he⟩
    have hD (i : Fin n) : 0 ≤ (k : Mat n) i i := Set.mem_iInter.mp hk.2 i
    exact hk.1 ((eq_one_of_lowerProjection_eq_zero he hD).symm ▸ hOne)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds h0)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε k hk
  by_contra h
  have hne : diagonalCutoff k * max 0 (ε - ‖L k‖) ≠ 0 := hk
  have hD (i : Fin n) : 0 ≤ (k : Mat n) i i := by
    by_contra hi
    have hprod : diagonalCutoff k = 0 :=
      Finset.prod_eq_zero (f := fun j : Fin n => max 0 ((k : Mat n) j j))
        (Finset.mem_univ i) (max_eq_left (le_of_lt (lt_of_not_ge hi)))
    exact hne (by simp [hprod])
  have hnorm : ‖L k‖ < ε := by
    by_contra hnorm
    have hb : max 0 (ε - ‖L k‖) = 0 :=
      max_eq_left (sub_nonpos.mpr (le_of_not_gt hnorm))
    exact hne (by rw [hb, mul_zero])
  have hmem : L k ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hnorm.trans hε.2
  exact hball hmem ⟨k, ⟨h, Set.mem_iInter.mpr hD⟩, rfl⟩

/-- The complex compact test with Haar integral one at positive radii. -/
def normalizedTest (n : ℕ) (ε : ℝ) : C(K n, ℂ) where
  toFun k := (((∫ y, rawTest n ε y ∂compactHaar n)⁻¹ * rawTest n ε k : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp (continuous_const.mul (rawTest n ε).continuous)

theorem integral_normalizedTest (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ k, normalizedTest n ε k ∂compactHaar n = 1 := by
  change (∫ k, (((∫ y, rawTest n ε y ∂compactHaar n)⁻¹ * rawTest n ε k : ℝ) : ℂ)
    ∂compactHaar n) = 1
  rw [integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ (rawTest_mass_pos n hε).ne',
    Complex.ofReal_one]

/-- The normalized lower-coordinate tests concentrate at the identity. -/
def RealCartanPeakTestStatement : Prop :=
  ∀ n : ℕ, (∀ ε > 0, ∫ k, normalizedTest n ε k ∂compactHaar n = 1) ∧
    ∀ U : Set (K n), IsOpen U → 1 ∈ U →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.support (normalizedTest n ε) ⊆ U

theorem realCartanPeakTest : RealCartanPeakTestStatement := by
  intro n
  refine ⟨fun _ hε => integral_normalizedTest n hε, fun U hU hOne => ?_⟩
  filter_upwards [eventually_support_rawTest_subset n hU hOne] with ε hε k hk
  apply hε
  intro hz
  exact hk (by simp [normalizedTest, hz])

end Langlands.Archimedean.RealCartanPeakTest
