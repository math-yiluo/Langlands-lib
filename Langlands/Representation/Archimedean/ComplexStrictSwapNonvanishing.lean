import Langlands.Representation.Archimedean.ComplexStrictSwapCell
import Langlands.Representation.Archimedean.ComplexLowerUnitaryCoordinate
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient

/-! # Nonvanishing of the complex strict swap product with an ordered source -/

noncomputable section

open scoped ComplexConjugate Manifold ContDiff Matrix Matrix.Norms.Operator
open MeasureTheory Filter Set Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
  ComplexJacquetNonvanishing ComplexPrincipalSeriesExtension ComplexGramFormula

variable {n : ℕ}

/-- The product of the squared moduli of the diagonal entries of a unitary matrix. -/
def diagonalPeak (k : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  ∏ i : Fin n, ‖k.val i i‖ ^ 2

private theorem continuous_diagonalPeak : Continuous (diagonalPeak (n := n)) :=
  continuous_finsetProd _ fun i _ =>
    (((continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)).norm).pow 2

@[simp]
private theorem diagonalPeak_one : diagonalPeak (1 : Matrix.unitaryGroup (Fin n) ℂ) = 1 := by
  simp [diagonalPeak]

private theorem unitary_row_sqNorm (k : Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j : Fin n, ‖k.val i j‖ ^ 2 = 1 := by
  have h : k.val * k.valᴴ = 1 := Unitary.mul_star_self_of_mem k.2
  have heq := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i) h
  change (k.val * k.valᴴ) i i = _ at heq
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at heq
  change (∑ j : Fin n, k.val i j * conj (k.val i j)) = (1 : ℂ) at heq
  have hreal := congrArg Complex.re heq
  simpa only [Complex.re_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re,
    Complex.one_re] using hreal

private theorem unitary_diag_sqNorm_le (k : Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ‖k.val i i‖ ^ 2 ≤ 1 := by
  rw [← unitary_row_sqNorm k i]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖k.val i j‖) (Finset.mem_univ i)

private theorem diagonalPeak_nonneg (k : Matrix.unitaryGroup (Fin n) ℂ) : 0 ≤ diagonalPeak k :=
  Finset.prod_nonneg fun i _ => sq_nonneg ‖k.val i i‖

private theorem diagonalPeak_le (k : Matrix.unitaryGroup (Fin n) ℂ) : diagonalPeak k ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => sq_nonneg ‖k.val i i‖) (fun i _ => unitary_diag_sqNorm_le k i)

private theorem diagonalPeak_eq_one_implies_upperTriangular
    (k : Matrix.unitaryGroup (Fin n) ℂ) (hk : diagonalPeak k = 1) :
    (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) ∈ upperTriangularSubgroup n ℂ := by
  have hdiag (i : Fin n) : ‖k.val i i‖ ^ 2 = 1 := by
    have hprod : ∏ j ∈ Finset.univ.erase i, ‖k.val j j‖ ^ 2 ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => sq_nonneg _) (fun j _ => unitary_diag_sqNorm_le k j)
    have hle : diagonalPeak k ≤ ‖k.val i i‖ ^ 2 := by
      unfold diagonalPeak
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (sq_nonneg ‖k.val i i‖)
    rw [hk] at hle
    exact (unitary_diag_sqNorm_le k i).antisymm hle
  rw [mem_upperTriangularSubgroup_iff]
  intro i j hji
  have hsum := unitary_row_sqNorm k i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag i] at hsum
  have hzero : ∑ b ∈ Finset.univ.erase i, ‖k.val i b‖ ^ 2 = 0 := by linarith
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖k.val i b‖)).mp hzero j
    (Finset.mem_erase.mpr ⟨hji.ne, Finset.mem_univ _⟩)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)

set_option maxHeartbeats 800000 in
private theorem continuous_phaseOrthPart (n : ℕ) :
    Continuous (phaseOrthPart (n := n)) := by
  have hZ : Continuous fun g : Langlands.GeneralLinear n ℂ => g.val := Units.continuous_val
  have hY : Continuous (fun g : Langlands.GeneralLinear n ℂ => g.val.map (starRingEnd ℂ)) :=
    continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hZ))
  have hcoord (i j : Fin n) :
      Continuous fun g : Langlands.GeneralLinear n ℂ =>
        hatCoord i j g.val (g.val.map (starRingEnd ℂ)) :=
    continuous_iff_continuousAt.mpr fun g =>
      ComplexMatrixCoefficientAnalytic.continuousAt_hatCoord hZ hY
        (fun l _ => ComplexMatrixCoefficientAnalytic.gram_conj_re_pos g l) i j
  exact (continuous_pi fun i => continuous_pi fun j => hcoord i j).subtype_mk _

@[simp]
private theorem phaseOrthPart_one (n : ℕ) : phaseOrthPart (1 : Langlands.GeneralLinear n ℂ) = 1 := by
  have h := phaseOrthPart_iwasawa (fun _ : Fin n => (1 : ℂˣ)) (1 : upperUnipotent n ℂ)
    (k := 1) (one_mem (unitaryCompact ℂ n))
  have hd : Iwasawa.diagonalUnits (fun _ : Fin n => (1 : ℂˣ)) = 1 :=
    map_one (Iwasawa.diagonalUnits (F := ℂ) (m := n))
  rw [hd, Subgroup.coe_one, one_mul, one_mul, phaseMatrix_one, one_mul] at h
  exact h

private theorem phaseMonomial_const_pow (k : Matrix.unitaryGroup (Fin n) ℂ) (p : ℕ → ℤ) (N : ℕ) :
    phaseMonomial n p (fun _ => N) k =
      phaseMonomial n p (fun _ => 0) k * (diagonalPeak k : ℂ) ^ N := by
  unfold phaseMonomial diagonalPeak
  rw [Complex.ofReal_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : (‖k.val i i‖ ^ 2 : ℝ) = Complex.normSq (k.val i i) :=
    (Complex.normSq_eq_norm_sq _).symm
  rw [h, ← Complex.mul_conj, mul_pow, add_zero, add_zero, pow_add, pow_add]
  ring

private abbrev phaseTest (n : ℕ) (ds : List ComplexCharacterData) (N : ℕ) :=
  phaseVector n (complexPositionExponent ds)
    (ComplexStrictLanglandsQuotient.complexPositionWeight ds) (fun _ => N)

private theorem phaseTest_mem (ds : List ComplexCharacterData) (N : ℕ) :
    phaseTest n ds N ∈ KFs n ds :=
  phaseVector_mem _ _ (ComplexStrictLanglandsQuotient.isPhasePower ds)
    (ComplexStrictLanglandsQuotient.complexPositionCharacter_phase ds)

private theorem phaseTest_pow (ds : List ComplexCharacterData) (N : ℕ)
    (g : Langlands.GeneralLinear n ℂ) :
    phaseTest n ds N g = phaseTest n ds 0 g * (diagonalPeak (phaseOrthPart g) : ℂ) ^ N := by
  unfold phaseTest phaseVector extension
  rw [phaseMonomial_const_pow, mul_assoc]

private theorem phaseTest_one (ds : List ComplexCharacterData) :
    phaseTest n ds 0 1 = 1 := by
  have h := phaseVector_unitary (ComplexStrictLanglandsQuotient.complexPositionWeight ds)
    (fun _ => 0) (e := complexPositionExponent ds)
    (1 : Matrix.unitaryGroup (Fin n) ℂ)
  simpa [phaseTest, phaseMonomial] using h

private theorem exists_integral_re_mul_pow_pos {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (F : X → ℂ) (q : X → ℝ) (hF : Integrable F μ)
    (hInt : ∀ N : ℕ, Integrable (fun x => (F x).re * q x ^ N) μ)
    (hq : ∀ x, 0 ≤ q x) {c δ b : ℝ} (hc : 0 ≤ c) (hδ : c < δ) (hb : 0 < b)
    (hOutside : ∀ x, (F x).re < 0 → q x ≤ c)
    {V : Set X} (hV : MeasurableSet V) (hV₀ : 0 < μ.real V) (hVtop : μ V ≠ ⊤)
    (hVb : ∀ x ∈ V, b ≤ (F x).re) (hVδ : ∀ x ∈ V, δ ≤ q x) :
    ∃ N : ℕ, 0 < ∫ x, (F x).re * q x ^ N ∂μ := by
  let M := ∫ x, ‖F x‖ ∂μ
  have hδ₀ : 0 < δ := hc.trans_lt hδ
  have hT : Tendsto (fun N : ℕ => (c / δ) ^ N * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hc hδ₀.le)
        ((div_lt_one hδ₀).mpr hδ)).mul_const M
  obtain ⟨N, hN⟩ := (hT.eventually (Iio_mem_nhds (mul_pos hV₀ hb))).exists
  change (c / δ) ^ N * M < μ.real V * b at hN
  rw [div_pow, div_mul_eq_mul_div] at hN
  have hsmall := (div_lt_iff₀ (pow_pos hδ₀ N)).mp hN
  let base : X → ℝ := V.indicator (fun _ => b * δ ^ N)
  have hbase : Integrable base μ :=
    (integrable_indicator_iff hV).mpr (integrableOn_const hVtop)
  have htail : Integrable (fun x => c ^ N * ‖F x‖) μ := hF.norm.const_mul _
  have hpoint (x : X) : base x - c ^ N * ‖F x‖ ≤ (F x).re * q x ^ N := by
    by_cases hx : x ∈ V
    · rw [show base x = b * δ ^ N from indicator_of_mem hx _]
      exact (sub_le_self _ (by positivity)).trans
        (mul_le_mul (hVb x hx) (pow_le_pow_left₀ hδ₀.le (hVδ x hx) N)
          (pow_nonneg hδ₀.le _) (hb.le.trans (hVb x hx)))
    · rw [show base x = 0 from indicator_of_notMem hx _, zero_sub]
      by_cases hnegative : (F x).re < 0
      · have hneg : -‖F x‖ ≤ (F x).re := (abs_le.mp (Complex.abs_re_le_norm _)).1
        have hpow := pow_le_pow_left₀ (hq x) (hOutside x hnegative) N
        calc
          _ ≤ -(q x ^ N) * ‖F x‖ := by
            rw [neg_mul]
            exact neg_le_neg (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))
          _ = -‖F x‖ * q x ^ N := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hneg (pow_nonneg (hq x) _)
      · exact (neg_nonpos.mpr (mul_nonneg (pow_nonneg hc _) (norm_nonneg _))).trans
          (mul_nonneg (le_of_not_gt hnegative) (pow_nonneg (hq x) _))
  have hint := integral_mono (hbase.sub htail) (hInt N) hpoint
  change (∫ x, base x - c ^ N * ‖F x‖ ∂μ) ≤ _ at hint
  rw [integral_sub hbase htail, show (∫ x, base x ∂μ) = μ.real V * (b * δ ^ N) by
    exact integral_indicator_const _ hV, integral_const_mul] at hint
  refine ⟨N, (sub_pos.mpr ?_).trans_le hint⟩
  calc
    c ^ N * M < μ.real V * b * δ ^ N := hsmall
    _ = _ := mul_assoc _ _ _

set_option maxHeartbeats 1000000 in
/-- The composite of strict adjacent swaps starting at a Langlands-ordered
complex standard module is nonzero. -/
theorem StrictSwapChain.intertwiner_ne_zero {ds es : List ComplexCharacterData} {m : ℕ}
    (w : StrictSwapChain n ds es m) (hn : ds.length = n) (ho : IsComplexLanglandsOrdered ds) :
    w.intertwiner ≠ 0 := by
  let g := (Langlands.GeneralLinear.permutation n ℂ w.permutation)⁻¹
  let L (z : Fin m → ℂ) := w.chartProduct z * g
  let F (z : Fin m → ℂ) := phaseTest n ds 0 (L z)
  let q (z : Fin m → ℂ) := diagonalPeak (phaseOrthPart (L z))
  have hL : Continuous L := w.continuous_chartProduct.mul continuous_const
  have hL₀ : L 0 = 1 := by
    change w.chartProduct (fun _ => 0) * g = 1
    rw [w.chartProduct_zero]
    exact mul_inv_cancel _
  have hLower (z : Fin m → ℂ) : L z ∈ lowerUnipotent n ℂ :=
    w.chartProduct_mul_permutation_inv_mem_lower hn ho z
  have hphaseCont : Continuous (phaseTest n ds 0) :=
    (mem_of_mem_kFs (phaseTest_mem ds 0)).1.continuous
  have hFRe : Continuous fun z => (F z).re := Complex.continuous_re.comp (hphaseCont.comp hL)
  have hq : Continuous q := continuous_diagonalPeak.comp ((continuous_phaseOrthPart n).comp hL)
  let S : Set (Langlands.GeneralLinear n ℂ) := {y | (1 / 2 : ℝ) < (phaseTest n ds 0 y).re}
  have hS : IsOpen S := isOpen_lt continuous_const (Complex.continuous_re.comp hphaseCont)
  have hS₁ : (1 : Langlands.GeneralLinear n ℂ) ∈ S := by
    change (1 / 2 : ℝ) < (phaseTest n ds 0 1).re
    rw [phaseTest_one, Complex.one_re]
    norm_num
  obtain ⟨c, hc, hc₁, hOutside⟩ := exists_bound_of_lowerUnitaryCoordinate diagonalPeak
    continuous_diagonalPeak diagonalPeak_le diagonalPeak_eq_one_implies_upperTriangular hS hS₁
  obtain ⟨δ, hcδ, hδ₁⟩ := exists_between hc₁
  let U : Set (Fin m → ℂ) := {z | (1 / 2 : ℝ) < (F z).re} ∩ {z | δ < q z}
  have hU : IsOpen U := (isOpen_lt continuous_const hFRe).inter (isOpen_lt continuous_const hq)
  have hU₀ : (0 : Fin m → ℂ) ∈ U := by
    change (1 / 2 : ℝ) < (phaseTest n ds 0 (L 0)).re ∧ δ < diagonalPeak (phaseOrthPart (L 0))
    rw [hL₀, phaseTest_one, phaseOrthPart_one, diagonalPeak_one, Complex.one_re]
    exact ⟨by norm_num, hδ₁⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU 0 hU₀
  let V := Metric.ball (0 : Fin m → ℂ) r
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hVpos : 0 < (volume : Measure (Fin m → ℂ)) V :=
    hVopen.measure_pos volume ⟨0, Metric.mem_ball_self hr⟩
  have hVfinite : (volume : Measure (Fin m → ℂ)) V < ⊤ := measure_ball_lt_top
  have hVreal : 0 < (volume : Measure (Fin m → ℂ)).real V :=
    ENNReal.toReal_pos hVpos.ne' hVfinite.ne
  have hFint : Integrable F := w.integrable_eval_chartProduct (mem_of_mem_kFs (phaseTest_mem ds 0)) g
  have hpoint (N : ℕ) (z : Fin m → ℂ) :
      (phaseTest n ds N (L z)).re = (F z).re * q z ^ N := by
    rw [phaseTest_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have htest (N : ℕ) : Integrable (fun z => phaseTest n ds N (L z)) :=
    w.integrable_eval_chartProduct (mem_of_mem_kFs (phaseTest_mem ds N)) g
  have hInt (N : ℕ) : Integrable (fun z => (F z).re * q z ^ N) :=
    (Complex.reCLM.integrable_comp (htest N)).congr (Eventually.of_forall (hpoint N))
  obtain ⟨N, hN⟩ := exists_integral_re_mul_pow_pos F q hFint hInt
    (fun _ => diagonalPeak_nonneg _) hc hcδ (b := 1 / 2) (by norm_num)
    (fun z hz => hOutside ⟨L z, hLower z⟩ (fun h => by
      change (1 / 2 : ℝ) < (F z).re at h
      linarith))
    hVopen.measurableSet hVreal hVfinite.ne (fun z hz => (hrU hz).1.le)
    (fun z hz => (hrU hz).2.le)
  let f : KFs n ds := ⟨phaseTest n ds N, phaseTest_mem ds N⟩
  have hvalue : (∫ z, (F z).re * q z ^ N) = ((w.intertwiner f).val g).re := by
    simp_rw [← hpoint N]
    rw [w.intertwiner_apply]
    exact integral_re (htest N)
  intro h
  rw [hvalue, h, LinearMap.zero_apply] at hN
  exact lt_irrefl 0 hN

end Langlands.Archimedean.ComplexSwapJacquet
