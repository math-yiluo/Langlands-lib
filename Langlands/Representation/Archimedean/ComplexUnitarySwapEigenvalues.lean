import Langlands.Representation.Archimedean.ComplexUnitaryCompactWitness

/-! The action of an adjacent-swap integral on the compact test vectors. -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator
open MeasureTheory Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

open ComplexBlock
open ComplexSwapJacquet hiding KFs

variable {n : ℕ} {pre post : List ComplexCharacterData} {d e : ComplexCharacterData}

private theorem blockMat_mul_outside {p : ℕ} (hp : p + 2 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) {i : Fin n} (hi : ∀ a, i ≠ pos p hp a) (j : Fin n) :
    (blockMat p hp M * Y) i j = Y i j := by
  have h : (blockMat p hp M * Y) i j = ((1 : Matrix (Fin n) (Fin n) ℂ) * Y) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [blockMat_apply_left p hp M hi k]
  rwa [Matrix.one_mul] at h

private theorem blockMat_mul_inside {p : ℕ} (hp : p + 2 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (a : Fin 2) (j : Fin n) :
    (blockMat p hp M * Y) (pos p hp a) j = ∑ b : Fin 2, M a b * Y (pos p hp b) j := by
  classical
  rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => k ∈ Set.range (pos p hp))]
  have hout : ∑ k : {k : Fin n // k ∉ Set.range (pos p hp)},
      blockMat p hp M (pos p hp a) k.1 * Y k.1 j = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [blockMat_apply_right p hp M _ (fun b hb => k.2 ⟨b, hb.symm⟩),
      Matrix.one_apply_ne (fun h => k.2 ⟨a, h⟩), zero_mul]
  rw [hout, add_zero]
  symm
  apply @Fintype.sum_equiv (Fin 2) {k : Fin n // k ∈ Set.range (pos p hp)} ℂ
    _ (Subtype.fintype _) _ (Equiv.ofInjective _ (pos_injective p hp))
  intro b
  change M a b * Y (pos p hp b) j = blockMat p hp M (pos p hp a) (pos p hp b) * Y (pos p hp b) j
  rw [blockMat_apply_pos]

private theorem testFactor_blockU_outside {p : ℕ} (hp : p + 2 ≤ n)
    (ij : Option (Fin n × Fin n))
    (ho : ∀ i j, ij = some (i, j) → ∀ a, i ≠ pos p hp a ∧ j ≠ pos p hp a)
    (M : Matrix.unitaryGroup (Fin 2) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    testFactor ij (↑(blockU p hp M * U) : Matrix (Fin n) (Fin n) ℂ) = testFactor ij U := by
  cases ij with
  | none => rfl
  | some ij =>
    rcases ij with ⟨i, j⟩
    have h := ho i j rfl
    simp only [testFactor, rowDifference, entrySq]
    have hi : (↑(blockU p hp M * U) : Matrix (Fin n) (Fin n) ℂ) i i = (U : Matrix (Fin n) (Fin n) ℂ) i i :=
      blockMat_mul_outside hp _ _ (fun a => (h a).1) i
    have hj : (↑(blockU p hp M * U) : Matrix (Fin n) (Fin n) ℂ) j i = (U : Matrix (Fin n) (Fin n) ℂ) j i :=
      blockMat_mul_outside hp _ _ (fun a => (h a).2) i
    rw [hi, hj]

private theorem chartCompact_mul_apply {p : ℕ} (hp : p + 2 ≤ n) (z : ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    let Y := blockMat p hp (chartCompact z : Matrix (Fin 2) (Fin 2) ℂ) * U
    Y (pos p hp 0) j = (starRingEnd ℂ z * U (pos p hp 0) j - U (pos p hp 1) j) / (chartRadius z : ℂ) ∧
    Y (pos p hp 1) j = (U (pos p hp 0) j + z * U (pos p hp 1) j) / (chartRadius z : ℂ) := by
  dsimp only
  rw [blockMat_mul_inside hp, blockMat_mul_inside hp, chartCompact_val]
  simp only [Fin.sum_univ_two]
  constructor
  · change (starRingEnd ℂ z / (chartRadius z : ℂ)) * U (pos p hp 0) j +
      (-1 / (chartRadius z : ℂ)) * U (pos p hp 1) j = _
    ring
  · change (1 / (chartRadius z : ℂ)) * U (pos p hp 0) j +
      (z / (chartRadius z : ℂ)) * U (pos p hp 1) j = _
    ring

private theorem rowDifference_chart_average {p : ℕ} (hp : p + 2 ≤ n) (z : ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    let i := pos p hp 0
    let j := pos p hp 1
    rowDifference i j (↑(blockU p hp (chartCompact z) * U) : Matrix (Fin n) (Fin n) ℂ) +
      rowDifference i j (↑(blockU p hp (chartCompact (-z)) * U) : Matrix (Fin n) (Fin n) ℂ) =
      2 * (1 - 2 / (chartNormSq z : ℂ)) * rowDifference i j U := by
  dsimp only
  let i := pos p hp 0
  let j := pos p hp 1
  let Y (w : ℂ) := blockMat p hp (chartCompact w : Matrix (Fin 2) (Fin 2) ℂ) *
    (U : Matrix (Fin n) (Fin n) ℂ)
  let a := (U : Matrix (Fin n) (Fin n) ℂ) i i
  let b := (U : Matrix (Fin n) (Fin n) ℂ) j i
  have hr : chartRadius (-z) = chartRadius z := by simp [chartRadius, chartNormSq]
  have hsq : (chartRadius z : ℂ) ^ 2 = (chartNormSq z : ℂ) := by
    exact_mod_cast chartRadius_sq z
  have hz : z * starRingEnd ℂ z = (chartNormSq z : ℂ) - 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, chartNormSq, Complex.ofReal_add, Complex.ofReal_one]
    ring
  have hne : (chartRadius z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (chartRadius_pos z).ne'
  have hA : (chartNormSq z : ℂ) ≠ 0 := hsq ▸ pow_ne_zero _ hne
  have hstar : star (chartRadius z : ℂ) = (chartRadius z : ℂ) := Complex.conj_ofReal _
  obtain ⟨h₀, h₁⟩ := chartCompact_mul_apply hp z (U : Matrix (Fin n) (Fin n) ℂ) i
  obtain ⟨h₂, h₃⟩ := chartCompact_mul_apply hp (-z) (U : Matrix (Fin n) (Fin n) ℂ) i
  change rowDifference i j (Y z) + rowDifference i j (Y (-z)) = _
  simp only [rowDifference, entrySq, show Y z i i = _ from h₀, show Y z j i = _ from h₁,
    show Y (-z) i i = _ from h₂, show Y (-z) j i = _ from h₃, hr, map_div₀, map_sub, map_add,
    map_neg, map_mul, starRingEnd_apply, star_star, hstar]
  have hcalc : ((star z * a - b) * (z * star a - star b) -
      (a + z * b) * (star a + star z * star b)) +
      ((-star z * a - b) * (-z * star a - star b) -
      (a + -z * b) * (star a + -star z * star b)) =
      2 * (z * star z - 1) * (a * star a - b * star b) := by ring
  change _ = 2 * (1 - 2 / (chartNormSq z : ℂ)) * (a * star a - b * star b)
  calc
    _ = (2 * (z * star z - 1) * (a * star a - b * star b)) / (chartRadius z : ℂ) ^ 2 := by
      rw [← hcalc]
      field_simp [hne]
      ring
    _ = _ := by
      rw [hsq, show z * star z = _ from hz]
      field_simp [hA]
      ring

private theorem integrable_radial (D : ℂ) (hD : 0 < D.re) : Integrable (swapRadial D) := by
  have hA (z : ℂ) : 0 < chartNormSq z := by unfold chartNormSq; positivity
  have hc : Continuous (swapRadial D) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_norm.pow 2)).log fun z => (hA z).ne')))
  have hdim : (Module.finrank ℝ ℂ : ℝ) < 2 + 2 * D.re := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℂ)) hdim).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => le_of_eq ?_)
  rw [swapRadial, Complex.norm_exp, Complex.re_mul_ofReal, ← show chartNormSq z = 1 + ‖z‖ ^ 2 from rfl,
    Real.rpow_def_of_pos (hA z), Complex.sub_re, Complex.neg_re, Complex.one_re]
  congr 1
  ring

private theorem integral_radial (D : ℂ) (hD : 0 < D.re) :
    ∫ z, swapRadial D z = (Real.pi : ℂ) / D := by
  have hβ : (-D - 1).re < -1 := by simp; linarith
  simpa only [swapRadial, chartNormSq, show -((-D - 1) + 1) = D by ring] using
    integral_one_add_norm_sq_cpow hβ

private theorem radial_div (D z : ℂ) : swapRadial D z / (chartNormSq z : ℂ) = swapRadial (D + 1) z := by
  have hp : 0 < chartNormSq z := by unfold chartNormSq; positivity
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hp.ne')).2
  have hA : Complex.exp (Real.log (chartNormSq z) : ℂ) = (chartNormSq z : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hp]
  calc
    swapRadial D z =
        swapRadial (D + 1) z * Complex.exp (Real.log (chartNormSq z) : ℂ) := by
      rw [swapRadial, swapRadial, ← Complex.exp_add]
      congr 1
      ring
    _ = _ := by rw [hA]

private theorem integral_radial_row (D : ℂ) (hD : 0 < D.re) :
    ∫ z, swapRadial D z * (1 - 2 / (chartNormSq z : ℂ)) =
      ((Real.pi : ℂ) / D) * ((1 - D) / (1 + D)) := by
  have hD' : 0 < (D + 1).re := by simp; linarith
  have hne := ne_zero_of_re_pos hD
  have hne' := ne_zero_of_re_pos hD'
  have heq (z : ℂ) : swapRadial D z * (1 - 2 / (chartNormSq z : ℂ)) =
      swapRadial D z - 2 * swapRadial (D + 1) z := by
    rw [mul_sub, mul_one, ← mul_div_assoc, mul_comm (swapRadial D z), mul_div_assoc, radial_div]
  simp only [heq]
  rw [integral_sub (integrable_radial D hD) ((integrable_radial (D + 1) hD').const_mul _),
    integral_const_mul, integral_radial D hD, integral_radial (D + 1) hD']
  rw [add_comm 1 D]
  field_simp [hne, hne']
  ring

/-- The common nonzero scalar of the adjacent swap on the base test. -/
def swapScalar (d : ComplexCharacterData) : ℂ := (-1 : ℂ) ^ d.weight * (2 * (Real.pi : ℂ))

theorem swapScalar_ne_zero (d : ComplexCharacterData) : swapScalar d ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (by norm_num)) (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))

/-- The ratio of the selected test's scalar to the base scalar. -/
def swapRatio {p : ℕ} (hp : p + 2 ≤ n) (D : ℂ) (ij : Option (Fin n × Fin n)) : ℂ :=
  if ij = some (pos p hp 0, pos p hp 1) then (1 - D) / (1 + D) else 1

private theorem integral_chart_test (p : ℕ) (hp : p + 2 ≤ n) (hpre : pre.length = p)
    (hre : 0 < (d.exponent - e.exponent).re) (hwt : d.weight = e.weight)
    (ij : Option (Fin n × Fin n))
    (hrows : ∀ i j, ij = some (i, j) → ij = some (pos p hp 0, pos p hp 1) ∨
      ∀ a, i ≠ pos p hp a ∧ j ≠ pos p hp a)
    (v : KFs n (pre ++ d :: e :: post))
    (hv : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      (v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) = compactTest (pre ++ d :: e :: post) ij U)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (2 * (d.exponent - e.exponent)) * ∫ z,
        (v : Langlands.GeneralLinear n ℂ → ℂ) (block p hp (ComplexGLTwoNoncompact.wn z) * Unitary.toUnits U) =
      swapScalar d * swapRatio hp (d.exponent - e.exponent) ij * compactTest (pre ++ d :: e :: post) ij U := by
  let D := d.exponent - e.exponent
  let ds := pre ++ d :: e :: post
  let F (z : ℂ) := (v : Langlands.GeneralLinear n ℂ → ℂ)
    (block p hp (ComplexGLTwoNoncompact.wn z) * Unitary.toUnits U)
  let P (z : ℂ) := testFactor ij (↑(blockU p hp (chartCompact z) * U) : Matrix (Fin n) (Fin n) ℂ)
  let N := nzFunction n ds (U : Matrix (Fin n) (Fin n) ℂ)
  let c := (-1 : ℂ) ^ d.weight
  have hF (z : ℂ) : F z = c * swapRadial D z * (N * P z) := by
    change (v : Langlands.GeneralLinear n ℂ → ℂ) _ = _
    rw [eval_block_chart p hp hpre, hv, compactTest, nzFunction_blockU p hp hpre hwt _ (chartCompact_det z)]
  have hD : D ≠ 0 := ne_zero_of_re_pos hre
  change (2 * D) * (∫ z, F z) = swapScalar d * swapRatio hp D ij * compactTest ds ij U
  by_cases hsel : ij = some (pos p hp 0, pos p hp 1)
  · let w := complexStandardRep n ds U v
    let i := pos p hp 0
    let j := pos p hp 1
    have hj := hj_pos p hp
    have hF' (z : ℂ) : F z = (w : Langlands.GeneralLinear n ℂ → ℂ) (ComplexSwapJacquet.chart i j hj z) := by
      simp only [F, w, principalSeriesRep_apply_coe, TranslateFinite.rightTranslation_apply,
        ComplexGLTwoNoncompact.wn, block_chart, i, j]
    have hFint : Integrable F := by
      rw [funext hF']
      obtain ⟨C, hC⟩ := ComplexGLTwoMoment.exists_bound_chart_rpow pre post d e i j
        (hi_pos p hp pre hpre) hj hre.le w.2.1
      exact ComplexGLTwoMoment.integrable_of_bound_rpow (contDiff_one_chart w.2.1).continuous.aestronglyMeasurable
        (by linarith only [hre]) hC
    let E := MeasurableEquiv.neg ℂ
    have hmp : MeasurePreserving E (volume : Measure ℂ) volume := Measure.measurePreserving_neg _
    have hsymm : ∫ z, F (-z) = ∫ z, F z := hmp.integral_comp E.measurableEmbedding F
    have hneg : Integrable (fun z => F (-z)) := (hmp.integrable_comp_emb E.measurableEmbedding).2 hFint
    have hrad (z : ℂ) : swapRadial D (-z) = swapRadial D z := by simp [swapRadial, chartNormSq]
    have hP (z : ℂ) : P z + P (-z) =
        2 * (1 - 2 / (chartNormSq z : ℂ)) * testFactor ij U := by
      simpa only [P, hsel, testFactor] using rowDifference_chart_average hp z U
    have hsum (z : ℂ) : F z + F (-z) =
        (2 * c * compactTest ds ij U) * (swapRadial D z * (1 - 2 / (chartNormSq z : ℂ))) := by
      rw [hF, hF, hrad, ← mul_add, ← mul_add, hP, compactTest]
      change _ = (2 * c * (N * testFactor ij U)) * _
      ring
    have havg := integral_add hFint hneg
    simp only [hsum, integral_const_mul, hsymm] at havg
    rw [integral_radial_row D hre] at havg
    have hmain : (∫ z, F z) =
        c * compactTest ds ij U * ((Real.pi : ℂ) / D * ((1 - D) / (1 + D))) := by
      linear_combination -havg / 2
    rw [hmain, swapRatio, ite_eq_left hsel, swapScalar]
    have hD' : 0 < (1 + D).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith only [hre]
    field_simp [hD, ne_zero_of_re_pos hD']
    ring
  · have ho : ∀ i j, ij = some (i, j) → ∀ a, i ≠ pos p hp a ∧ j ≠ pos p hp a :=
      fun i j hij => (hrows i j hij).resolve_left hsel
    have hpoint (z : ℂ) : F z = (c * compactTest ds ij U) * swapRadial D z := by
      rw [hF, show P z = testFactor ij U from testFactor_blockU_outside hp ij ho _ U, compactTest]
      change _ = (c * (N * testFactor ij U)) * _
      ring
    simp only [hpoint, integral_const_mul, integral_radial D hre, swapRatio, ite_eq_right hsel, swapScalar, mul_one]
    field_simp [hD]
    ring

/-- The adjacent swap is nonzero and carries each admissible compact test to its stated scalar
multiple, as functions on the compact group. -/
theorem exists_test_swap (hn : (pre ++ d :: e :: post).length = n)
    (p : ℕ) (hp : p + 2 ≤ n) (hpre : pre.length = p)
    (hre : 0 < (d.exponent - e.exponent).re) (hwt : d.weight = e.weight) :
    ∃ S : KFs n (pre ++ d :: e :: post) →ₗ[ℂ] KFs n (pre ++ e :: d :: post),
      IsComplexStandardIntertwining n (complexStandardRep n (pre ++ e :: d :: post))
        (complexStandardLie n (pre ++ e :: d :: post)) (pre ++ d :: e :: post) S ∧
      ∀ (ij : Option (Fin n × Fin n)),
        (∀ i j, ij = some (i, j) → ij = some (pos p hp 0, pos p hp 1) ∨
          ∀ a, i ≠ pos p hp a ∧ j ≠ pos p hp a) →
        ∀ v : KFs n (pre ++ d :: e :: post),
          (∀ U : Matrix.unitaryGroup (Fin n) ℂ,
            (v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) = compactTest (pre ++ d :: e :: post) ij U) →
          ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
            (S v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) =
              swapScalar d * swapRatio hp (d.exponent - e.exponent) ij * compactTest (pre ++ d :: e :: post) ij U := by
  obtain ⟨v, hv⟩ := exists_testVector (n := n) (pre ++ d :: e :: post) none
  have hone := compactTest_one (n := n) (pre ++ d :: e :: post) none (by simp)
  have heval : ComplexBlock.lamN p hp pre post d e hpre hn hre.le 1 v = swapScalar d := by
    rw [lamN_one_eq_integral hn p hp hpre hre]
    simpa [ComplexGLTwoNoncompact.wn, block_chart, swapRatio, hone] using
      integral_chart_test p hp hpre hre hwt none (by simp) v hv 1
  have hne : lamN p hp pre post d e hpre hn hre.le 1 ≠ 0 := by
    intro h
    rw [h, LinearMap.zero_apply] at heval
    exact swapScalar_ne_zero d heval.symm
  obtain ⟨S, hS, hEval⟩ := exists_swap_integral hn p hp hpre hre hne
  refine ⟨S, hS, fun ij hrows f hf U => ?_⟩
  exact (hEval f U).trans (integral_chart_test p hp hpre hre hwt ij hrows f hf U)

end Langlands.Archimedean.ComplexUnitary
