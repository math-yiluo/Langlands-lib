import Langlands.Representation.Archimedean.ComplexBlockRestriction
import Langlands.Representation.Archimedean.ComplexGLTwoMomentJacquetProof
import Langlands.Representation.Archimedean.ComplexStandardHomTransposeProof
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction
import Langlands.Representation.Archimedean.TranslateFinite

/-! The convergent rank-one intertwiner on the positive side of the wall. -/

noncomputable section

open scoped ContDiff Manifold Matrix Matrix.Norms.Operator
open MeasureTheory Filter Langlands.GeneralLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean ComplexSwapJacquet

variable {n : ℕ} {pre post : List ComplexCharacterData} {d e : ComplexCharacterData}

theorem lamN_one_eq_integral (hn : (pre ++ d :: e :: post).length = n)
    (p : ℕ) (hp : p + 2 ≤ n) (hpre : pre.length = p)
    (hre : 0 < (d.exponent - e.exponent).re) (v : KFs n (pre ++ d :: e :: post)) :
    ComplexBlock.lamN p hp pre post d e hpre hn hre.le 1 v =
      (2 * (d.exponent - e.exponent)) * ∫ z,
        (v : Langlands.GeneralLinear n ℂ → ℂ)
          (ComplexSwapJacquet.chart (ComplexBlock.pos p hp 0) (ComplexBlock.pos p hp 1) (ComplexBlock.hj_pos p hp) z) := by
  let i := ComplexBlock.pos p hp 0
  let j := ComplexBlock.pos p hp 1
  have hi : (i : ℕ) = pre.length := ComplexBlock.hi_pos p hp pre hpre
  have hj : (j : ℕ) = i + 1 := ComplexBlock.hj_pos p hp
  let f : Langlands.GeneralLinear n ℂ → ℂ := v
  let φ : ℂ → ℂ := fun z => f (ComplexSwapJacquet.chart i j hj z)
  have hf : f ∈ complexStandardModule n (pre ++ d :: e :: post) := v.2.1
  let r : ℝ := 2 + 2 * (d.exponent - e.exponent).re
  have hr : 2 < r := by
    change 2 < 2 + 2 * (d.exponent - e.exponent).re
    linarith only [hre]
  obtain ⟨C, hC⟩ := ComplexGLTwoMoment.exists_bound_chart_rpow pre post d e i j hi hj hre.le hf
  let g := rightDerivative (matrixModel ℂ n) (Matrix.single j j 1) f -
    kappa (pre ++ d :: e :: post) hn i 1 • f
  have hg : g ∈ complexStandardModule n (pre ++ d :: e :: post) :=
    Submodule.sub_mem _ (rightDerivative_mem_principalSeries _ hf _) (Submodule.smul_mem _ _ hf)
  have hgz (z : ℂ) : g (ComplexSwapJacquet.chart i j hj z) = fderiv ℝ φ z z := by
    simp only [g, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rightDerivative_chart_diag_j hn hj hf,
      one_mul, φ]
    ring
  obtain ⟨C', hC'⟩ := ComplexGLTwoMoment.exists_bound_chart_rpow pre post d e i j hi hj hre.le hg
  have hφ : ContDiff ℝ 1 φ := contDiff_one_chart hf
  have hD (z : ℂ) : ‖fderiv ℝ φ z z‖ ≤ C' * (1 + ‖z‖) ^ (-r) := by
    rw [← hgz]
    exact hC' z
  have hEuler := ComplexGLTwoMoment.integral_fderiv_apply_self_rpow (C := max C C') (r := r) hφ hr
    (fun z => (hC z).trans (mul_le_mul_of_nonneg_right (le_max_left C C') (by positivity)))
    (fun z => (hD z).trans (mul_le_mul_of_nonneg_right (le_max_right C C') (by positivity)))
  have hint := ComplexGLTwoMoment.integrable_of_bound_rpow hφ.continuous.aestronglyMeasurable hr hC
  have hint' : Integrable (fun z => fderiv ℝ φ z z) := ComplexGLTwoMoment.integrable_of_bound_rpow
    (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_id).aestronglyMeasurable) hr hD
  have hκ : kappa (pre ++ d :: e :: post) hn i 1 - kappa (pre ++ d :: e :: post) hn j 1 =
      2 * (d.exponent - e.exponent) + 2 := by
    have hj' : (j : ℕ) = pre.length + 1 := by omega
    rw [kappa_eq, kappa_eq, hi, hj', posExponent_append_cons, posExponent_append_cons_succ]
    simp only [Complex.one_re, Complex.one_im, Complex.ofReal_zero, Complex.ofReal_one, mul_one,
      mul_zero, zero_add]
    push_cast
    ring
  have hpt (z : ℂ) : integrand (pre ++ d :: e :: post) hn i j hj 1 f z =
      ((2 * (d.exponent - e.exponent) + 2) * φ z) + fderiv ℝ φ z z := by
    rw [integrand, rightDerivative_chart_diag_j hn hj hf, one_mul, ← hκ]
    dsimp [φ]
    ring
  rw [ComplexBlock.lamN, functional_apply]
  change (∫ z, integrand (pre ++ d :: e :: post) hn i j hj 1 f z) =
    (2 * (d.exponent - e.exponent)) * ∫ z, φ z
  simp only [hpt]
  rw [integral_add (hint.const_mul _) hint', integral_const_mul, hEuler]
  ring

/-- A nonzero convergent integral gives an adjacent-swap intertwiner with this compact
restriction formula. -/
theorem exists_swap_integral (hn : (pre ++ d :: e :: post).length = n)
    (p : ℕ) (hp : p + 2 ≤ n) (hpre : pre.length = p)
    (hre : 0 < (d.exponent - e.exponent).re)
    (hne : ComplexBlock.lamN p hp pre post d e hpre hn hre.le 1 ≠ 0) :
    ∃ S : KFs n (pre ++ d :: e :: post) →ₗ[ℂ] KFs n (pre ++ e :: d :: post),
      IsComplexStandardIntertwining n (complexStandardRep n (pre ++ e :: d :: post))
        (complexStandardLie n (pre ++ e :: d :: post)) (pre ++ d :: e :: post) S ∧
      ∀ (v : KFs n (pre ++ d :: e :: post)) (k : Matrix.unitaryGroup (Fin n) ℂ),
        (S v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) =
          (2 * (d.exponent - e.exponent)) * ∫ z,
            (v : Langlands.GeneralLinear n ℂ → ℂ)
              (ComplexBlock.block p hp (ComplexSwapJacquet.chart (0 : Fin 2) 1 ComplexBlock.hj_two z) *
                Unitary.toUnits k) := by
  have hes : (pre ++ e :: d :: post).length = n := by
    simpa only [List.length_append, List.length_cons] using hn
  obtain ⟨S, hSone, hS⟩ := ComplexBlock.exists_embedding_eval_one _ _ hes _ hne
    (ComplexBlock.isJacquet_lamN p hp pre post d e hpre hn hes hre.le 1)
  have hSint := ComplexPermutation.intertwining_of_embedding hS
  refine ⟨S, hSint, fun v k => ?_⟩
  have heq : S (complexStandardRep n (pre ++ d :: e :: post) k v) =
      complexStandardRep n (pre ++ e :: d :: post) k (S v) :=
    ComplexStandardHomTransposeProof.map_complexStandardRep hSint k v
  have hv := hSone (complexStandardRep n (pre ++ d :: e :: post) k v)
  rw [heq] at hv
  rw [lamN_one_eq_integral hn p hp hpre hre] at hv
  simpa only [principalSeriesRep_apply_coe, TranslateFinite.rightTranslation_apply, one_mul,
    ComplexBlock.block_chart] using hv

end Langlands.Archimedean.ComplexUnitary
