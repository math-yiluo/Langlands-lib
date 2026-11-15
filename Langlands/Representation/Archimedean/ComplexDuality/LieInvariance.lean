import Langlands.Global.ArchimedeanCompact
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Infinitesimal invariance of the integral over `U(n)` of products of principal-series functions

Let `f` lie in the smooth principal series of `GL(n, ℂ)` for characters `χ`, and `h` in the one
for characters `χ'` with `χ i z * χ' i z = 1`. For every complex matrix `X` and every
left-invariant finite measure `μ` on `U(n)` (`unitaryCompact ℂ n`), the main theorem
`integral_rightDerivative_mul_add_eq_zero` states

`∫_{U(n)} (R(X) f) h dμ + ∫_{U(n)} f (R(X) h) dμ = 0`,

where `R(X)` is the right derivative `rightDerivative (matrixModel ℂ n) X`.

## Proof route

Write `Φ = f̃ h̃` for the product of the extensions of `f` and `h` to the invertible matrices
(`productExtension`). Then `(R(X) f) h + f (R(X) h) = DΦ(k)(k X)`. At a unitary `k`, put
`Z = k X kᴴ`, so `k X = Z k`, and decompose `Z = Σ_{a,b} Z_ab E_ab`.

* For `a < b`, `Φ` is invariant under the upper unipotent group, so `DΦ(k)(E_ab k) = 0`.
* For `a = b`, `Φ` transforms under the diagonal torus by the product of the characters of
  `χ` and `χ'`, which is `∏ᵢ |aᵢ|^{2(n-1-2i)}`; the derivative is `2 Re Z_aa (n - 1 - 2a) Φ(k)`.
* For `b < a`, `Z_ab E_ab = Re Z_ab (E_ab - E_ba) + Im Z_ab · i (E_ab + E_ba) + conj Z_ab E_ba`
  (`single_eq_skew`); the last term is again killed by unipotent invariance, and the product
  rule turns the first two into the pair term `pairTerm` (derivatives of `Re Z_ab · Φ`,
  `Im Z_ab · Φ` along skew-Hermitian left-invariant directions) minus
  `2 (Re Z_bb - Re Z_aa) Φ(k)`.

The multiples of `Φ(k)` cancel by the counting identity `sum_sum_ite_lt_sub`, so pointwise
`DΦ(k)(k X)` is a sum of pair terms (`fderiv_mul_eq_sum_pairTerm`). Each pair term integrates to
zero by `integral_fderiv_mul_eq_zero`: for `Y` skew-Hermitian, `t ↦ ∫ Ψ(exp(tY) k) dμ` is constant
by left invariance, and differentiating under the integral at `t = 0` gives
`∫ DΨ(k)(Y k) dμ = 0`.

The auxiliary declarations live in the namespace
`Langlands.Archimedean.ComplexDuality.LieInvariance`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate Topology

namespace Langlands.Archimedean.ComplexDuality

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Matrix MeasureTheory

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

namespace LieInvariance

/-! ## The unitary group as a compact space -/

theorem continuous_unitaryCompact_val :
    Continuous fun k : unitaryCompact ℂ n =>
      ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isCompact_unitaryCompact :
    IsCompact (unitaryCompact ℂ n : Set (Langlands.GeneralLinear n ℂ)) := by
  have : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    isCompact_iff_compactSpace.mp (Langlands.Global.isCompact_unitaryMatrix ℂ n)
  have h : (unitaryCompact ℂ n : Set (Langlands.GeneralLinear n ℂ)) =
      Set.range (Unitary.toUnits :
        Matrix.unitaryGroup (Fin n) ℂ → Langlands.GeneralLinear n ℂ) := by
    ext g
    constructor
    · intro hg
      exact ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ), hg⟩, Units.ext rfl⟩
    · rintro ⟨u, rfl⟩
      exact u.2
  rw [h]
  exact isCompact_range continuous_unitary_toUnits

instance compactSpace_unitaryCompact : CompactSpace (unitaryCompact ℂ n) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryCompact

/-- `exp(t Y)` is unitary for `Y` skew-Hermitian. -/
theorem exp_smul_mem_unitaryGroup {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = -Y) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hs : star (t • Y) = -(t • Y) := by
    rw [star_smul, Matrix.star_eq_conjTranspose, hY, star_trivial, smul_neg]
  have h1 : NormedSpace.exp (t • Y) * star (NormedSpace.exp (t • Y)) = 1 := by
    rw [NormedSpace.star_exp, hs, ← NormedSpace.exp_add_of_commute (Commute.neg_right rfl),
      add_neg_cancel, NormedSpace.exp_zero]
  exact Matrix.mem_unitaryGroup_iff.mpr h1


/-! ## Skew-Hermitian directions and coefficient functions -/

/-- The skew-Hermitian matrix `E_ab - E_ba`. -/
def skewRe (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single a b 1 - Matrix.single b a 1

/-- The skew-Hermitian matrix `i (E_ab + E_ba)`. -/
def skewIm (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single a b Complex.I + Matrix.single b a Complex.I

theorem star_skewRe (a b : Fin n) : star (skewRe a b) = -skewRe a b := by
  rw [Matrix.star_eq_conjTranspose, skewRe, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, neg_sub]

theorem star_skewIm (a b : Fin n) : star (skewIm a b) = -skewIm a b := by
  rw [Matrix.star_eq_conjTranspose, skewIm, Matrix.conjTranspose_add,
    Matrix.conjTranspose_single, Matrix.conjTranspose_single, Complex.star_def, Complex.conj_I,
    ← Matrix.single_neg, ← Matrix.single_neg, neg_add, add_comm]

/-- Every matrix unit decomposes into the two skew-Hermitian directions plus the transposed
matrix unit. -/
theorem single_eq_skew (a b : Fin n) (z : ℂ) :
    Matrix.single a b z = z.re • skewRe a b + z.im • skewIm a b + Matrix.single b a (star z) := by
  ext i j
  simp only [skewRe, skewIm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.single_apply]
  by_cases hP : a = i ∧ b = j <;> by_cases hQ : b = i ∧ a = j
  · simp only [ite_eq_left hP, ite_eq_left hQ]
    apply Complex.ext <;> simp
  · simp only [ite_eq_left hP, ite_eq_right hQ]
    apply Complex.ext <;> simp
  · simp only [ite_eq_right hP, ite_eq_left hQ]
    apply Complex.ext <;> simp
  · simp only [ite_eq_right hP, ite_eq_right hQ]
    simp

/-- The real-linear functional `M ↦ Re M_ab`, with complex values. -/
def reEntryCLM (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)))

/-- The real-linear functional `M ↦ Im M_ab`, with complex values. -/
def imEntryCLM (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (Complex.imCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)))

theorem reEntryCLM_apply (a b : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) :
    reEntryCLM a b M = ((M a b).re : ℂ) := by
  simp [reEntryCLM]

theorem imEntryCLM_apply (a b : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) :
    imEntryCLM a b M = ((M a b).im : ℂ) := by
  simp [imEntryCLM]

/-- The coefficient `Re (y X yᴴ)_ab`. -/
def coeffRe (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (((y * X * star y) a b).re : ℂ)

/-- The coefficient `Im (y X yᴴ)_ab`. -/
def coeffIm (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (((y * X * star y) a b).im : ℂ)

theorem differentiableAt_sandwich (X k : Matrix (Fin n) (Fin n) ℂ) :
    DifferentiableAt ℝ (fun y : Matrix (Fin n) (Fin n) ℂ => y * X * star y) k :=
  (((hasFDerivAt_id (𝕜 := ℝ) k).mul_const' X).mul'
    (HasFDerivAt.star (hasFDerivAt_id (𝕜 := ℝ) k))).differentiableAt

theorem fderiv_sandwich_apply (X k V : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (fun y : Matrix (Fin n) (Fin n) ℂ => y * X * star y) k V =
      V * X * star k + k * X * star V := by
  have h : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => y * X * star y) _ k :=
    ((hasFDerivAt_id (𝕜 := ℝ) k).mul_const' X).mul'
      (HasFDerivAt.star (hasFDerivAt_id (𝕜 := ℝ) k))
  rw [h.fderiv]
  simp [add_comm]

theorem contDiff_sandwich (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => y * X * star y :=
  (contDiff_id.mul contDiff_const).mul
    (starL' ℝ : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ).contDiff

theorem coeffRe_eq (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    coeffRe X a b = reEntryCLM a b ∘ fun y : Matrix (Fin n) (Fin n) ℂ => y * X * star y := by
  funext y
  simp [coeffRe, reEntryCLM_apply]

theorem coeffIm_eq (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    coeffIm X a b = imEntryCLM a b ∘ fun y : Matrix (Fin n) (Fin n) ℂ => y * X * star y := by
  funext y
  simp [coeffIm, imEntryCLM_apply]

theorem contDiff_coeffRe (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ContDiff ℝ ∞ (coeffRe X a b) := by
  rw [coeffRe_eq]
  exact (reEntryCLM a b).contDiff.comp (contDiff_sandwich X)

theorem contDiff_coeffIm (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ContDiff ℝ ∞ (coeffIm X a b) := by
  rw [coeffIm_eq]
  exact (imEntryCLM a b).contDiff.comp (contDiff_sandwich X)

theorem fderiv_coeffRe_apply (X k V : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    fderiv ℝ (coeffRe X a b) k V = (((V * X * star k + k * X * star V) a b).re : ℂ) := by
  rw [coeffRe_eq, ((reEntryCLM a b).hasFDerivAt.comp k
    (differentiableAt_sandwich X k).hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply, fderiv_sandwich_apply, reEntryCLM_apply]

theorem fderiv_coeffIm_apply (X k V : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    fderiv ℝ (coeffIm X a b) k V = (((V * X * star k + k * X * star V) a b).im : ℂ) := by
  rw [coeffIm_eq, ((imEntryCLM a b).hasFDerivAt.comp k
    (differentiableAt_sandwich X k).hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply, fderiv_sandwich_apply, imEntryCLM_apply]

theorem sandwich_skew_eq {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y)
    (X k : Matrix (Fin n) (Fin n) ℂ) :
    Y * k * X * star k + k * X * star (Y * k) = Y * (k * X * star k) - k * X * star k * Y := by
  rw [star_mul, hY]
  simp only [Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg]

/-- The derivative of `Re (y X yᴴ)_ab` along `E_ab - E_ba` at `k` is `Re (Z_bb - Z_aa)`,
`Z = k X kᴴ`. -/
theorem fderiv_coeffRe_skewRe (X k : Matrix (Fin n) (Fin n) ℂ) {a b : Fin n} (hab : a ≠ b) :
    fderiv ℝ (coeffRe X a b) k (skewRe a b * k) =
      ((((k * X * star k) b b).re - ((k * X * star k) a a).re : ℝ) : ℂ) := by
  rw [fderiv_coeffRe_apply, sandwich_skew_eq (star_skewRe a b)]
  simp [skewRe, Matrix.sub_mul, Matrix.mul_sub, hab, hab.symm]

/-- The derivative of `Im (y X yᴴ)_ab` along `i (E_ab + E_ba)` at `k` is `Re (Z_bb - Z_aa)`,
`Z = k X kᴴ`. -/
theorem fderiv_coeffIm_skewIm (X k : Matrix (Fin n) (Fin n) ℂ) {a b : Fin n} (hab : a ≠ b) :
    fderiv ℝ (coeffIm X a b) k (skewIm a b * k) =
      ((((k * X * star k) b b).re - ((k * X * star k) a a).re : ℝ) : ℂ) := by
  rw [fderiv_coeffIm_apply, sandwich_skew_eq (star_skewIm a b)]
  simp [skewIm, Matrix.add_mul, Matrix.mul_add, hab, hab.symm]

/-! ## Derivatives of functions equivariant under the upper triangular Borel subgroup -/

/-- The product of the principal-series characters of `χ` and of `χ'`, for inverse
characters. -/
theorem principalSeriesCharacter_mul_eq {χ χ' : ℕ → ℂˣ → ℂ} (hχ : ∀ i z, χ i z * χ' i z = 1)
    (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n χ a * principalSeriesCharacter ℂ n χ' a =
      ∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) := by
  simp only [principalSeriesCharacter, Complex.finrank_real_complex, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  linear_combination
    (((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
      ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) * hχ i (a i)

theorem principalSeriesCharacter_mul_one {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ i z, χ i z * χ' i z = 1) :
    principalSeriesCharacter ℂ n χ 1 * principalSeriesCharacter ℂ n χ' 1 = 1 := by
  rw [principalSeriesCharacter_mul_eq hχ]
  simp

theorem ofReal_norm_exp_sq_cpow (z s : ℂ) :
    ((‖Complex.exp z‖ ^ 2 : ℝ) : ℂ) ^ s = Complex.exp (2 * (z.re : ℂ) * s) := by
  have h : ((‖Complex.exp z‖ ^ 2 : ℝ) : ℂ) = Complex.exp ((2 * z.re : ℝ) : ℂ) := by
    rw [Complex.norm_exp, ← Complex.ofReal_exp, sq, ← Real.exp_add, two_mul]
  rw [h, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
  · push_cast
    ring
  · simp [Real.pi_pos]
  · simp [Real.pi_pos.le]

/-- A function invariant under left multiplication by upper unipotent matrices has zero
derivative along `N y` for `N` strictly upper triangular. -/
theorem fderiv_strictUpper_mul_eq_zero {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {y : Matrix (Fin n) (Fin n) ℂ} (hΦd : DifferentiableAt ℝ Φ y)
    (hΦ : ∀ u : upperUnipotent n ℂ,
      Φ (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * y) = Φ y)
    {N : Matrix (Fin n) (Fin n) ℂ} (hN : ∀ i j, j ≤ i → N i j = 0) :
    fderiv ℝ Φ y (N * y) = 0 := by
  have hupper : ∀ t : ℝ, (1 + t • N).IsUpperTriangular := fun t i j hij => by
    have hne : i ≠ j := fun h => (lt_irrefl _ (h ▸ hij))
    simp [Matrix.one_apply_ne hne, hN i j hij.le]
  have hdiag : ∀ (t : ℝ) (i : Fin n), (1 + t • N) i i = 1 := fun t i => by
    simp [hN i i le_rfl]
  have hunit : ∀ t : ℝ, IsUnit (1 + t • N) := fun t => by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular (hupper t)]
    simp [hdiag t]
  let u : ℝ → upperUnipotent n ℂ := fun t => ⟨(hunit t).unit, hupper t, hdiag t⟩
  have hγ : HasDerivAt (fun t : ℝ => (1 + t • N) * y) (N * y) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const N).const_add 1).mul_const y
    simpa using h
  have hcomp := hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hconst : (Φ ∘ fun t : ℝ => (1 + t • N) * y) = fun _ => Φ y := by
    funext t
    exact hΦ (u t)
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 _)

/-- The weight `n - 1 - 2i` of the position `i`. -/
def positionWeight (n : ℕ) (i : Fin n) : ℂ :=
  (n : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)

/-- A function transforming under the diagonal torus by the product of the characters of
inverse principal series has derivative `Σᵢ 2 Re dᵢ (n - 1 - 2i) Φ(y)` along `diag(d) y`. -/
theorem fderiv_diagonal_mul_eq {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {y : Matrix (Fin n) (Fin n) ℂ} (hΦd : DifferentiableAt ℝ Φ y)
    (hΦ : ∀ a : Fin n → ℂˣ, Φ (Matrix.diagonal (fun i => (a i : ℂ)) * y) =
      (∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) * Φ y)
    (d : Fin n → ℂ) :
    fderiv ℝ Φ y (Matrix.diagonal d * y) =
      (∑ i : Fin n, 2 * ((d i).re : ℂ) * positionWeight n i) * Φ y := by
  set Λ : ℂ := ∑ i : Fin n, 2 * ((d i).re : ℂ) * positionWeight n i
  let a : ℝ → Fin n → ℂˣ := fun t i => Units.mk0 (Complex.exp ((t : ℂ) * d i))
    (Complex.exp_ne_zero _)
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • Matrix.diagonal d) =
      Matrix.diagonal fun i => (a t i : ℂ) := fun t => by
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    simp [a, Complex.real_smul]
  have hγ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Matrix.diagonal d) * y)
      (Matrix.diagonal d * y) 0 := by
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.diagonal d) 0).mul_const y
    simpa using h
  have hcomp := hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hchar : ∀ t : ℝ, (∏ i : Fin n,
      ((‖(a t i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((‖(a t i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) =
      Complex.exp ((t : ℂ) * Λ) := fun t => by
    simp only [a, Units.val_mk0, ofReal_norm_exp_sq_cpow, ← Complex.exp_add,
      ← Complex.exp_sum]
    congr 1
    simp only [Λ, Finset.mul_sum, positionWeight]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.re_ofReal_mul]
    push_cast
    ring
  have hfun : (Φ ∘ fun t : ℝ => NormedSpace.exp (t • Matrix.diagonal d) * y) =
      fun t : ℝ => Complex.exp ((t : ℂ) * Λ) * Φ y := by
    funext t
    simp only [Function.comp_apply, hexp, hΦ, hchar]
  rw [hfun] at hcomp
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Λ) * Φ y) (Λ * Φ y) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Λ).cexp).mul_const (Φ y)
    simpa using h
  exact hcomp.unique hd

/-! ## The counting identity -/

theorem sum_sum_ite_lt_sub (x : Fin n → ℂ) :
    ∑ a : Fin n, ∑ b : Fin n, (if b < a then x b - x a else 0) =
      ∑ i : Fin n, x i * positionWeight n i := by
  have h1 : ∑ a : Fin n, ∑ b : Fin n, (if b < a then x a else 0) =
      ∑ a : Fin n, x a * ((a : ℕ) : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul, mul_comm]
  have h2 : ∑ a : Fin n, ∑ b : Fin n, (if b < a then x b else 0) =
      ∑ b : Fin n, x b * ((n : ℂ) - 1 - ((b : ℕ) : ℂ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul, mul_comm]
    have hb := b.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have h3 : ∀ a : Fin n, ∑ b : Fin n, (if b < a then x b - x a else 0) =
      ∑ b : Fin n, (if b < a then x b else 0) - ∑ b : Fin n, (if b < a then x a else 0) := by
    intro a
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun a _ => h3 a, Finset.sum_sub_distrib, h1, h2,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [positionWeight]
  ring

/-! ## The pointwise identity -/

/-- The term of the pair `(a, b)`: the derivatives of `Re Z_ab · Φ` and of `Im Z_ab · Φ` at `k`
along the skew-Hermitian directions `(E_ab - E_ba) k` and `i (E_ab + E_ba) k`. -/
def pairTerm (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (X k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ℂ :=
  fderiv ℝ (fun y => coeffRe X a b y * Φ y) k (skewRe a b * k) +
    fderiv ℝ (fun y => coeffIm X a b y * Φ y) k (skewIm a b * k)

theorem single_strictUpper {r s : Fin n} (hrs : r < s) (w : ℂ) :
    ∀ i j, j ≤ i → Matrix.single r s w i j = 0 := by
  intro i j hji
  rw [Matrix.single_apply, ite_eq_right_iff]
  rintro ⟨h1, h2⟩
  subst h1
  subst h2
  exact absurd hji (not_le.mpr hrs)

section Pointwise

variable {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} {k : Matrix (Fin n) (Fin n) ℂ}

/-- The derivative of `Φ` along `Z_ab E_ab k`, `Z = k X kᴴ`, is the term of the pair `(a, b)`
up to multiples of `Φ k`. -/
theorem fderiv_single_mul_eq (hΦd : DifferentiableAt ℝ Φ k)
    (hunip : ∀ u : upperUnipotent n ℂ,
      Φ (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * k) = Φ k)
    (hdiag : ∀ a : Fin n → ℂˣ, Φ (Matrix.diagonal (fun i => (a i : ℂ)) * k) =
      (∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) * Φ k)
    (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    fderiv ℝ Φ k (Matrix.single a b ((k * X * star k) a b) * k) =
      (if b < a then pairTerm Φ X k a b else 0) +
        ((if a = b then 2 * (((k * X * star k) a a).re : ℂ) * positionWeight n a else 0) -
          (if b < a then 2 * (((k * X * star k) b b).re : ℂ) -
            2 * (((k * X * star k) a a).re : ℂ) else 0)) * Φ k := by
  rcases lt_trichotomy b a with hba | rfl | hab
  · have hne : a ≠ b := hba.ne'
    simp only [ite_eq_left hba, ite_eq_right hne]
    have hE1 : fderiv ℝ Φ k
        (Matrix.single b a (star ((k * X * star k) a b)) * k) = 0 :=
      fderiv_strictUpper_mul_eq_zero hΦd hunip (single_strictUpper hba _)
    have hRe := fderiv_fun_mul
      (((contDiff_coeffRe X a b).differentiable (by simp)).differentiableAt (x := k)) hΦd
    have hIm := fderiv_fun_mul
      (((contDiff_coeffIm X a b).differentiable (by simp)).differentiableAt (x := k)) hΦd
    rw [single_eq_skew, Matrix.add_mul, Matrix.add_mul, map_add, map_add, hE1,
      Matrix.smul_mul, Matrix.smul_mul, map_smul, map_smul, pairTerm, hRe, hIm]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
      fderiv_coeffRe_skewRe X k hne, fderiv_coeffIm_skewIm X k hne, coeffRe, coeffIm,
      Complex.real_smul]
    push_cast
    ring
  · simp only [lt_irrefl, ite_false, ite_true, zero_add, sub_zero]
    rw [← Matrix.diagonal_single, fderiv_diagonal_mul_eq hΦd hdiag,
      Finset.sum_eq_single b (fun i _ hi => by simp [Pi.single_eq_of_ne hi])
        (fun h => absurd (Finset.mem_univ b) h)]
    simp
  · have hne : a ≠ b := hab.ne
    have hnlt : ¬b < a := not_lt.mpr hab.le
    simp only [ite_eq_right hnlt, ite_eq_right hne, add_zero, sub_self, zero_mul]
    exact fderiv_strictUpper_mul_eq_zero hΦd hunip (single_strictUpper hab _)

/-- Pointwise, the derivative of `Φ` at a unitary `k` along `k X` is the sum of the terms of
the pairs `b < a`: the multiples of `Φ k` cancel by the counting identity. -/
theorem fderiv_mul_eq_sum_pairTerm (hΦd : DifferentiableAt ℝ Φ k)
    (hunip : ∀ u : upperUnipotent n ℂ,
      Φ (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * k) = Φ k)
    (hdiag : ∀ a : Fin n → ℂˣ, Φ (Matrix.diagonal (fun i => (a i : ℂ)) * k) =
      (∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) * Φ k)
    (hk : star k * k = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ Φ k (k * X) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then pairTerm Φ X k a b else 0 := by
  have hkX : k * X = (k * X * star k) * k := by
    rw [Matrix.mul_assoc (k * X), hk, Matrix.mul_one]
  have hsum : fderiv ℝ Φ k ((k * X * star k) * k) = ∑ a : Fin n, ∑ b : Fin n,
      fderiv ℝ Φ k (Matrix.single a b ((k * X * star k) a b) * k) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (k * X * star k)]
    simp only [Finset.sum_mul, map_sum]
  have hcount : ∑ a : Fin n, ∑ b : Fin n,
      (if b < a then 2 * (((k * X * star k) b b).re : ℂ) -
        2 * (((k * X * star k) a a).re : ℂ) else 0) =
      ∑ i : Fin n, 2 * (((k * X * star k) i i).re : ℂ) * positionWeight n i :=
    sum_sum_ite_lt_sub fun i => 2 * (((k * X * star k) i i).re : ℂ)
  have hdsum : ∑ a : Fin n, ∑ b : Fin n,
      (if a = b then 2 * (((k * X * star k) a a).re : ℂ) * positionWeight n a else 0) =
      ∑ i : Fin n, 2 * (((k * X * star k) i i).re : ℂ) * positionWeight n i := by
    simp [Finset.sum_ite_eq]
  have hzero : ∑ a : Fin n, ∑ b : Fin n,
      ((if a = b then 2 * (((k * X * star k) a a).re : ℂ) * positionWeight n a else 0) -
        (if b < a then 2 * (((k * X * star k) b b).re : ℂ) -
          2 * (((k * X * star k) a a).re : ℂ) else 0)) * Φ k = 0 := by
    simp only [← Finset.sum_mul, Finset.sum_sub_distrib, hdsum, hcount, sub_self, zero_mul]
  rw [hkX, hsum, Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    fderiv_single_mul_eq hΦd hunip hdiag X a b]
  simp only [Finset.sum_add_distrib, hzero, add_zero]

end Pointwise

/-! ## Products of principal-series functions with inverse characters -/

section PrincipalSeriesProduct

variable {χ : ℕ → ℂˣ → ℂ} {f : Langlands.GeneralLinear n ℂ → ℂ}

/-- The product `f̃ h̃` of the extensions of two functions to the matrices. -/
def productExtension (f h : Langlands.GeneralLinear n ℂ → ℂ) (y : Matrix (Fin n) (Fin n) ℂ) :
    ℂ :=
  unitsExtension f y * unitsExtension h y

theorem unitsExtension_unipotent_mul (hf : f ∈ principalSeries ℂ n χ)
    (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    unitsExtension f (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        (g : Matrix (Fin n) (Fin n) ℂ)) =
      principalSeriesCharacter ℂ n χ 1 * f g := by
  rw [← Units.val_mul, unitsExtension_val]
  have h := ((mem_principalSeries_iff ℂ n χ f).mp hf).2 1 u g
  rwa [map_one, one_mul] at h

theorem unitsExtension_diagonal_mul (hf : f ∈ principalSeries ℂ n χ) (a : Fin n → ℂˣ)
    (g : Langlands.GeneralLinear n ℂ) :
    unitsExtension f (Matrix.diagonal (fun i => (a i : ℂ)) * (g : Matrix (Fin n) (Fin n) ℂ)) =
      principalSeriesCharacter ℂ n χ a * f g := by
  have h := ((mem_principalSeries_iff ℂ n χ f).mp hf).2 a 1 g
  rw [Subgroup.coe_one, mul_one] at h
  rw [show Matrix.diagonal (fun i => (a i : ℂ)) * (g : Matrix (Fin n) (Fin n) ℂ) =
      ((Iwasawa.diagonalUnits a * g : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) by
    rw [Units.val_mul, Iwasawa.diagonalUnits_val], unitsExtension_val, h]

end PrincipalSeriesProduct

theorem contDiffOn_one_of_infty {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {s : Set (Matrix (Fin n) (Fin n) ℂ)} (h : ContDiffOn ℝ ∞ Ψ s) : ContDiffOn ℝ 1 Ψ s :=
  h.of_le (by exact_mod_cast le_top)

/-- For `Ψ` of class `C¹` on the invertible matrices, `k ↦ DΨ(k)(V k)` is continuous on
`U(n)`. -/
theorem continuous_fderiv_apply_val {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hΨ : ContDiffOn ℝ 1 Ψ {y | IsUnit y})
    {V : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hV : Continuous V) :
    Continuous fun k : unitaryCompact ℂ n =>
      fderiv ℝ Ψ ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
        (V ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) :=
  ((hΨ.continuousOn_fderiv_of_isOpen isOpen_setOf_isUnit_matrix le_rfl).comp_continuous
    continuous_unitaryCompact_val fun _ => Units.isUnit _).clm_apply
    (hV.comp continuous_unitaryCompact_val)

section Integral

variable [MeasurableSpace (unitaryCompact ℂ n)] [BorelSpace (unitaryCompact ℂ n)]
  (μ : Measure (unitaryCompact ℂ n))

theorem integrable_of_continuous [IsFiniteMeasure μ] {φ : unitaryCompact ℂ n → ℂ}
    (hφ : Continuous φ) : Integrable φ μ :=
  (BoundedContinuousFunction.mkOfCompact ⟨φ, hφ⟩).integrable μ

/-! ## Integration by parts along a direction of `𝔲(n)` -/

/-- For `Ψ` of class `C¹` on the invertible matrices and `Y ∈ 𝔲(n)`, the integral over `U(n)`
of the derivative of `Ψ` along the left-invariant direction `Y k` vanishes. -/
theorem integral_fderiv_mul_eq_zero [μ.IsMulLeftInvariant] [IsFiniteMeasure μ]
    {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΨ : ContDiffOn ℝ 1 Ψ {y | IsUnit y})
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = -Y) :
    ∫ k, fderiv ℝ Ψ ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
      (Y * ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) ∂μ = 0 := by
  let kv : unitaryCompact ℂ n → Matrix (Fin n) (Fin n) ℂ := fun k =>
    ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
  let E : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => NormedSpace.exp (t • Y)
  have hE : ∀ t, E t ∈ Matrix.unitaryGroup (Fin n) ℂ := exp_smul_mem_unitaryGroup hY
  let u : ℝ → unitaryCompact ℂ n := fun t => ⟨Unitary.toUnits ⟨E t, hE t⟩, hE t⟩
  have hu : ∀ t k, kv (u t * k) = E t * kv k := fun _ _ => rfl
  have hEc : Continuous E := NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have hkc : Continuous kv := continuous_unitaryCompact_val
  have hunit : ∀ t k, IsUnit (E t * kv k) := fun t k =>
    (Matrix.isUnit_exp _).mul (Units.isUnit _)
  have hopen := isOpen_setOf_isUnit_matrix (F := ℂ) (N := n)
  have hdiff : ∀ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y → DifferentiableAt ℝ Ψ y := fun y hy =>
    (hΨ.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hy)
  have hfd : ContinuousOn (fderiv ℝ Ψ) {y | IsUnit y} :=
    hΨ.continuousOn_fderiv_of_isOpen hopen le_rfl
  have hΨc : ContinuousOn Ψ {y | IsUnit y} := hΨ.continuousOn
  let F : ℝ → unitaryCompact ℂ n → ℂ := fun t k => Ψ (E t * kv k)
  let F' : ℝ → unitaryCompact ℂ n → ℂ := fun t k => fderiv ℝ Ψ (E t * kv k) (Y * E t * kv k)
  have hp : Continuous fun x : ℝ × unitaryCompact ℂ n => E x.1 * kv x.2 :=
    (hEc.comp continuous_fst).mul (hkc.comp continuous_snd)
  have hG : Continuous fun x : ℝ × unitaryCompact ℂ n => F' x.1 x.2 :=
    (hfd.comp_continuous hp fun x => hunit x.1 x.2).clm_apply
      ((continuous_const.mul (hEc.comp continuous_fst)).mul (hkc.comp continuous_snd))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod isCompact_univ).exists_bound_of_continuousOn
    hG.continuousOn
  have hFc : ∀ t, Continuous (F t) := fun t =>
    hΨc.comp_continuous ((continuous_const).mul hkc) fun k => hunit t k
  have hF'c : Continuous (F' 0) := hG.comp (Continuous.prodMk_right 0)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (x₀ := 0)
    (bound := fun _ => C) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    (integrable_of_continuous μ (hFc 0)) (hF'c.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun k t ht =>
      hC (t, k) ⟨Metric.ball_subset_closedBall ht, Set.mem_univ _⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ => by
      have h1 : HasDerivAt (fun s : ℝ => E s * kv k) (Y * E t * kv k) t :=
        (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y t).mul_const (kv k)
      exact (hdiff _ (hunit t k)).hasFDerivAt.comp_hasDerivAt t h1)
  have hconst : (fun t => ∫ k, F t k ∂μ) = fun _ => ∫ k, Ψ (kv k) ∂μ := by
    funext t
    exact integral_mul_left_eq_self (fun k => Ψ (kv k)) (u t)
  have h0 := hderiv.2
  rw [hconst] at h0
  have h00 := h0.unique (hasDerivAt_const 0 _)
  have hF'0 : ∀ k, F' 0 k = fderiv ℝ Ψ (kv k) (Y * kv k) := fun k => by
    simp only [F', E, zero_smul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul]
  simp only [hF'0] at h00
  exact h00

end Integral

end LieInvariance

open LieInvariance

section Integral

variable [MeasurableSpace (unitaryCompact ℂ n)] [BorelSpace (unitaryCompact ℂ n)]
  (μ : Measure (unitaryCompact ℂ n))

/-- **Infinitesimal invariance.** For `f` in the principal series of `χ` and `h` in that of
the inverse characters `χ'`, the integral over `U(n)` of `(R(X) f) h + f (R(X) h)` vanishes,
for every left-invariant finite measure on `U(n)` and every complex matrix `X`. -/
theorem integral_rightDerivative_mul_add_eq_zero [μ.IsMulLeftInvariant] [IsFiniteMeasure μ]
    (χ χ' : ℕ → ℂˣ → ℂ) (hχ : ∀ i z, χ i z * χ' i z = 1)
    {f h : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ)
    (hh : h ∈ principalSeries ℂ n χ') (X : Matrix (Fin n) (Fin n) ℂ) :
    (∫ k, rightDerivative (matrixModel ℂ n) X f (k : Langlands.GeneralLinear n ℂ) * h k ∂μ) +
      ∫ k, f (k : Langlands.GeneralLinear n ℂ) *
        rightDerivative (matrixModel ℂ n) X h k ∂μ = 0 := by
  have hfs := ((mem_principalSeries_iff ℂ n χ f).mp hf).1
  have hhs := ((mem_principalSeries_iff ℂ n χ' h).mp hh).1
  let kv : unitaryCompact ℂ n → Matrix (Fin n) (Fin n) ℂ := fun k =>
    ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hkc : Continuous kv := continuous_unitaryCompact_val
  have hΦ : ContDiffOn ℝ ∞ (productExtension f h) {y | IsUnit y} :=
    (contDiffOn_unitsExtension hfs).mul (contDiffOn_unitsExtension hhs)
  have hΦd : ∀ k : unitaryCompact ℂ n, DifferentiableAt ℝ (productExtension f h) (kv k) :=
    fun k => (hΦ.differentiableOn (by simp)).differentiableAt
      (isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit _))
  have hunip : ∀ (k : unitaryCompact ℂ n) (u : upperUnipotent n ℂ),
      productExtension f h (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        kv k) = productExtension f h (kv k) := fun k u => by
    simp only [productExtension, kv, unitsExtension_unipotent_mul hf,
      unitsExtension_unipotent_mul hh, unitsExtension_val]
    linear_combination (f k * h k) * principalSeriesCharacter_mul_one hχ
  have hdiag : ∀ (k : unitaryCompact ℂ n) (a : Fin n → ℂˣ),
      productExtension f h (Matrix.diagonal (fun i => (a i : ℂ)) * kv k) =
        (∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
          ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) *
          productExtension f h (kv k) := fun k a => by
    simp only [productExtension, kv, unitsExtension_diagonal_mul hf,
      unitsExtension_diagonal_mul hh, unitsExtension_val]
    rw [← principalSeriesCharacter_mul_eq hχ a]
    ring
  have hkk : ∀ k : unitaryCompact ℂ n, star (kv k) * kv k = 1 := fun k =>
    Matrix.mem_unitaryGroup_iff'.mp k.2
  have hpt : ∀ k : unitaryCompact ℂ n,
      rightDerivative (matrixModel ℂ n) X f (k : Langlands.GeneralLinear n ℂ) * h k +
        f (k : Langlands.GeneralLinear n ℂ) * rightDerivative (matrixModel ℂ n) X h k =
      ∑ a : Fin n, ∑ b : Fin n,
        if b < a then pairTerm (productExtension f h) X (kv k) a b else 0 := fun k => by
    rw [← fderiv_mul_eq_sum_pairTerm (hΦd k) (hunip k) (hdiag k) (hkk k) X,
      rightDerivative_eq_fderiv hfs, rightDerivative_eq_fderiv hhs]
    have hd := fderiv_fun_mul
      (differentiableAt_unitsExtension hfs (Units.isUnit (k : Langlands.GeneralLinear n ℂ)))
      (differentiableAt_unitsExtension hhs (Units.isUnit (k : Langlands.GeneralLinear n ℂ)))
    rw [show productExtension f h = fun y => unitsExtension f y * unitsExtension h y from rfl, hd]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, unitsExtension_val, kv]
    ring
  have hRe : ∀ a b : Fin n, ContDiffOn ℝ 1
      (fun y => coeffRe X a b y * productExtension f h y) {y | IsUnit y} := fun a b =>
    contDiffOn_one_of_infty ((contDiff_coeffRe X a b).contDiffOn.mul hΦ)
  have hIm : ∀ a b : Fin n, ContDiffOn ℝ 1
      (fun y => coeffIm X a b y * productExtension f h y) {y | IsUnit y} := fun a b =>
    contDiffOn_one_of_infty ((contDiff_coeffIm X a b).contDiffOn.mul hΦ)
  have hcont : ∀ a b : Fin n, Continuous fun k : unitaryCompact ℂ n =>
      if b < a then pairTerm (productExtension f h) X (kv k) a b else 0 := fun a b => by
    by_cases hba : b < a
    · simp only [hba, ite_true, pairTerm]
      exact (continuous_fderiv_apply_val (hRe a b)
          (V := fun y => skewRe a b * y) (continuous_const.mul continuous_id)).add
        (continuous_fderiv_apply_val (hIm a b)
          (V := fun y => skewIm a b * y) (continuous_const.mul continuous_id))
    · simp only [hba, ite_false]
      exact continuous_const
  have hint : ∀ a b : Fin n, ∫ k, (if b < a then
      pairTerm (productExtension f h) X (kv k) a b else 0) ∂μ = 0 := fun a b => by
    by_cases hba : b < a
    · simp only [hba, ite_true, pairTerm]
      have hY1 : (skewRe a b)ᴴ = -skewRe a b := by
        rw [← Matrix.star_eq_conjTranspose, star_skewRe]
      have hY2 : (skewIm a b)ᴴ = -skewIm a b := by
        rw [← Matrix.star_eq_conjTranspose, star_skewIm]
      rw [integral_add
        (integrable_of_continuous μ
          (continuous_fderiv_apply_val (hRe a b)
          (V := fun y => skewRe a b * y) (continuous_const.mul continuous_id)))
        (integrable_of_continuous μ
          (continuous_fderiv_apply_val (hIm a b)
          (V := fun y => skewIm a b * y) (continuous_const.mul continuous_id))),
        integral_fderiv_mul_eq_zero μ (hRe a b) hY1, integral_fderiv_mul_eq_zero μ (hIm a b) hY2,
        add_zero]
    · simp [hba]
  have hA : Continuous fun k : unitaryCompact ℂ n =>
      rightDerivative (matrixModel ℂ n) X f (k : Langlands.GeneralLinear n ℂ) * h k :=
    ((contMDiff_rightDerivative hfs X).continuous.comp continuous_subtype_val).mul
      (hhs.continuous.comp continuous_subtype_val)
  have hB : Continuous fun k : unitaryCompact ℂ n =>
      f (k : Langlands.GeneralLinear n ℂ) * rightDerivative (matrixModel ℂ n) X h k :=
    (hfs.continuous.comp continuous_subtype_val).mul
      ((contMDiff_rightDerivative hhs X).continuous.comp continuous_subtype_val)
  rw [← integral_add (integrable_of_continuous μ hA) (integrable_of_continuous μ hB)]
  simp only [hpt]
  rw [integral_finsetSum _ fun a _ => integrable_of_continuous μ
    (continuous_finsetSum _ fun b _ => hcont a b)]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_of_continuous μ (hcont a b)]
  exact Finset.sum_eq_zero fun b _ => hint a b

end Integral

end Langlands.Archimedean.ComplexDuality
