import Langlands.Representation.Archimedean.ComplexGLTwoWirtinger
import Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrderingReduction
import Langlands.Representation.Archimedean.ComplexSwapJacquetProof
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-!
# The noncompact picture of the `GL_2(ℂ)` principal series

Let `d 0`, `d 1` be complex characters with exponents `t_0`, `t_1` and weights `l_0`, `l_1`, and
let `X(d)` be the `U(2)`-finite functions of the standard module of `d`. Write
`C(z) = w n(z) = [[0, 1], [1, z]]` and `φ_f(z) = f(C(z))` (`ncp f`). With
`p = t_0 - t_1 + (l_0 - l_1)/2` and `q = t_0 - t_1 - (l_0 - l_1)/2`, and `∂`, `∂̄` the Wirtinger
derivatives of `φ = φ_f`, the right derivatives act on `φ_f` by

* `R(c E_01) f ↦ c ∂φ + c̄ ∂̄φ`;
* `R(c E_10) f ↦ -c (z² ∂φ + (p + 1) z φ) - c̄ (z̄² ∂̄φ + (q + 1) z̄ φ)`;
* `R(i E_00) f ↦ i l_1 φ - i z ∂φ + i z̄ ∂̄φ`.

The `E_10` formula comes from the matrix identity
`C(z) (c E_10) = (c E_01) C(z) - (c z E_00) C(z) + (c z E_11) C(z) + C(z) (-c z² E_01)`;
the other two are the chart formulas of `ComplexSwapJacquetLie`. Consequently the operators
`D = (R(E_01) - i R(i E_01))/2`, `D̄ = (R(E_01) + i R(i E_01))/2`,
`F = (R(E_10) - i R(i E_10))/2`, `F̄ = (R(E_10) + i R(i E_10))/2` and `H = R(i E_00)` act by
`∂`, `∂̄`, `-z² ∂ - (p + 1) z`, `-z̄² ∂̄ - (q + 1) z̄` and `i l_1 - i z ∂ + i z̄ ∂̄`.
-/

noncomputable section

open scoped TensorProduct Matrix

open Complex ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace ComplexGLTwoNoncompact

/-! ## The chart -/

theorem hj01 : ((1 : Fin 2) : ℕ) = ((0 : Fin 2) : ℕ) + 1 := rfl

/-- The chart `C(z) = w n(z) = [[0, 1], [1, z]]`. -/
abbrev wn (z : ℂ) : Langlands.GeneralLinear 2 ℂ :=
  ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z

theorem wn_val (z : ℂ) :
    ((wn z : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, z] := by
  rw [ComplexSwapJacquet.chart_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.swap, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply]

theorem weyl_mul_unipotent (z : ℂ) :
    complexGLTwoWeyl * complexGLTwoUnipotent z = wn z := by
  apply Units.ext
  rw [Units.val_mul, wn_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [complexGLTwoWeyl, complexGLTwoUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The noncompact picture `φ_f(z) = f(w n(z))`. -/
def ncp (f : Langlands.GeneralLinear 2 ℂ → ℂ) (z : ℂ) : ℂ := f (wn z)

/-- `C(z) (c E_10) = (c E_01) C(z) - (c z E_00) C(z) + (c z E_11) C(z) + C(z) (-c z² E_01)`. -/
theorem wn_mul_single_one_zero (z c : ℂ) :
    ((wn z : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.single 1 0 c =
      Matrix.single 0 1 c * (wn z : Matrix (Fin 2) (Fin 2) ℂ) +
        Matrix.single 0 0 (-(c * z)) * (wn z : Matrix (Fin 2) (Fin 2) ℂ) +
        Matrix.single 1 1 (c * z) * (wn z : Matrix (Fin 2) (Fin 2) ℂ) +
        (wn z : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.single 0 1 (-(c * z ^ 2)) := by
  rw [wn_val]
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-! ## The characters -/

section Characters

variable (d : Fin 2 → ComplexCharacterData)

/-- `p = t_0 - t_1 + (l_0 - l_1)/2`. -/
def pp : ℂ := (d 0).exponent - (d 1).exponent + (((d 0).weight - (d 1).weight : ℤ) : ℂ) / 2

/-- `q = t_0 - t_1 - (l_0 - l_1)/2`. -/
def qq : ℂ := (d 0).exponent - (d 1).exponent - (((d 0).weight - (d 1).weight : ℤ) : ℂ) / 2

/-- `κ_k(c)` in Wirtinger form: `κ_k(c) = ((a_k + l_k)/2) c + ((a_k - l_k)/2) c̄` with
`a_0 = 2 t_0 + 1` and `a_1 = 2 t_1 - 1`. -/
theorem kappa_ofFn (k : Fin 2) (c : ℂ) :
    ComplexSwapJacquet.kappa (List.ofFn d) List.length_ofFn k c =
      ((2 * (d k).exponent + 1 - 2 * ((k : ℕ) : ℂ) + ((d k).weight : ℂ)) / 2) * c +
        ((2 * (d k).exponent + 1 - 2 * ((k : ℕ) : ℂ) - ((d k).weight : ℂ)) / 2) * conj c := by
  have hre : ((c.re : ℝ) : ℂ) = (c + conj c) / 2 := by
    rw [Complex.re_eq_add_conj]
  have him : ((c.im : ℝ) : ℂ) = (c - conj c) / (2 * Complex.I) := by
    rw [Complex.im_eq_sub_conj]
  unfold ComplexSwapJacquet.kappa
  rw [hre, him]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  fin_cases k <;> simp <;> field_simp <;> ring_nf

end Characters

/-! ## Right derivatives in the noncompact picture -/

section Derivatives

variable {d : Fin 2 → ComplexCharacterData} {f : Langlands.GeneralLinear 2 ℂ → ℂ}

theorem fderiv_ncp_apply (f : Langlands.GeneralLinear 2 ℂ → ℂ) (z w : ℂ) :
    fderiv ℝ (ncp f) z w = dz (ncp f) z * w + dzb (ncp f) z * conj w :=
  fderiv_apply_eq _ z w

/-- `R(c E_01) f ↦ c ∂φ + c̄ ∂̄φ`. -/
theorem ncp_single01 (hf : f ∈ complexStandardModule 2 (List.ofFn d)) (c z : ℂ) :
    ncp (rightDerivative (matrixModel ℂ 2) (Matrix.single 0 1 c) f) z =
      c * dz (ncp f) z + conj c * dzb (ncp f) z := by
  rw [ncp, ComplexSwapJacquet.rightDerivative_chart_single_ij hj01 hf.1]
  change fderiv ℝ (ncp f) z c = _
  rw [fderiv_ncp_apply]
  ring

/-- `R(c E_00) f ↦ κ_1(c) φ - Dφ(z)(c z)`. -/
theorem ncp_single00 (hf : f ∈ complexStandardModule 2 (List.ofFn d)) (c z : ℂ) :
    ncp (rightDerivative (matrixModel ℂ 2) (Matrix.single 0 0 c) f) z =
      ComplexSwapJacquet.kappa (List.ofFn d) List.length_ofFn 1 c * ncp f z -
        (dz (ncp f) z * (c * z) + dzb (ncp f) z * conj (c * z)) := by
  rw [ncp, (ComplexSwapJacquet.chartLieFacts _ List.length_ofFn 0 1 hj01).diag_i f hf c z]
  change _ * ncp f z - fderiv ℝ (ncp f) z (c * z) = _
  rw [fderiv_ncp_apply]

/-- `R(c E_11) f ↦ κ_0(c) φ + Dφ(z)(c z)`. -/
theorem ncp_single11 (hf : f ∈ complexStandardModule 2 (List.ofFn d)) (c z : ℂ) :
    ncp (rightDerivative (matrixModel ℂ 2) (Matrix.single 1 1 c) f) z =
      ComplexSwapJacquet.kappa (List.ofFn d) List.length_ofFn 0 c * ncp f z +
        (dz (ncp f) z * (c * z) + dzb (ncp f) z * conj (c * z)) := by
  rw [ncp, (ComplexSwapJacquet.chartLieFacts _ List.length_ofFn 0 1 hj01).diag_j f hf c z]
  change _ * ncp f z + fderiv ℝ (ncp f) z (c * z) = _
  rw [fderiv_ncp_apply]

theorem single01_strictUpper (c : ℂ) :
    ∀ a b : Fin 2, b ≤ a → (Matrix.single 0 1 c : Matrix (Fin 2) (Fin 2) ℂ) a b = 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- `R(c E_10) f (C(z)) = (κ_0(-c z) + κ_1(c z)) f(C(z)) + Dφ(z)(-c z²)`. -/
theorem rightDerivative_wn_single10 (hf : f ∈ complexStandardModule 2 (List.ofFn d))
    (c z : ℂ) :
    rightDerivative (matrixModel ℂ 2) (Matrix.single 1 0 c) f (wn z) =
      (ComplexSwapJacquet.kappa (List.ofFn d) List.length_ofFn 0 (-(c * z)) +
          ComplexSwapJacquet.kappa (List.ofFn d) List.length_ofFn 1 (c * z)) * f (wn z) +
        fderiv ℝ (ncp f) z (-(c * z ^ 2)) := by
  rw [rightDerivative_eq_fderiv hf.1, wn_mul_single_one_zero, map_add, map_add, map_add,
    ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero
      (differentiableAt_unitsExtension hf.1 (Units.isUnit (wn z)))
      (fun u => ComplexSwapJacquet.unitsExtension_unipotent_mul_eq hf u (wn z))
      (single01_strictUpper c),
    ComplexSwapJacquet.fderiv_unitsExtension_single_mul List.length_ofFn hf 0 _ (wn z),
    ComplexSwapJacquet.fderiv_unitsExtension_single_mul List.length_ofFn hf 1 _ (wn z),
    ← rightDerivative_eq_fderiv hf.1,
    ComplexSwapJacquet.rightDerivative_chart_single_ij hj01 hf.1]
  change 0 + _ + _ + fderiv ℝ (ncp f) z _ = _
  ring

/-- `R(c E_10) f ↦ -c (z² ∂φ + (p + 1) z φ) - c̄ (z̄² ∂̄φ + (q + 1) z̄ φ)`. -/
theorem ncp_single10 (hf : f ∈ complexStandardModule 2 (List.ofFn d)) (c z : ℂ) :
    ncp (rightDerivative (matrixModel ℂ 2) (Matrix.single 1 0 c) f) z =
      -c * (z ^ 2 * dz (ncp f) z + (pp d + 1) * z * ncp f z) -
        conj c * (conj z ^ 2 * dzb (ncp f) z + (qq d + 1) * conj z * ncp f z) := by
  rw [ncp, rightDerivative_wn_single10 hf, kappa_ofFn, kappa_ofFn, fderiv_ncp_apply]
  change _ * ncp f z + _ = _
  simp only [pp, qq, map_neg, map_mul, map_pow, Fin.val_zero, Fin.val_one]
  push_cast
  ring

end Derivatives

end ComplexGLTwoNoncompact

end Langlands.Archimedean
