import Langlands.Representation.Archimedean.ComplexGramFormula
import Langlands.Representation.Archimedean.PrincipalSeriesMatrixCoefficientAnalytic

/-!
# Analyticity of `U(n)`-finite matrix coefficients of complex principal series

For a `U(n)`-finite function `f` of a principal series of `GL_n(ℂ)`, a continuous `φ` on `U(n)`
and a finite measure on `U(n)`, the matrix coefficient `t ↦ ∫ f(κ g exp(tH)) φ(κ) dμ(κ)` along a
real diagonal one-parameter subgroup is real analytic. Consequently the annihilator, in an
integral pairing over `U(n)`, of a `(𝔤, K)`-stable space of such functions is invariant under all
of `GL_n(ℂ)` (`matrixCoefficient_eq_zero`). This is the unitary counterpart of the Library module
`PrincipalSeriesMatrixCoefficientAnalytic`, using the polarized Gram formula of
`ComplexGramFormula`.
-/

noncomputable section

open Matrix MeasureTheory Metric Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate ComplexOrder

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace ComplexMatrixCoefficientAnalytic

open ComplexGramFormula MatrixCoefficientAnalytic

variable {n : ℕ}

/-! ## Complex differentiability of polarized Gram expressions along curves -/

section Differentiable

variable {Z Y : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}

theorem differentiableAt_paddedGram (hZ : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z)
    (hY : ∀ p q, DifferentiableAt ℂ (fun w => Y w p q) z) (i : ℕ) (p q : Fin n) :
    DifferentiableAt ℂ (fun w => paddedGram i (Z w) (Y w) p q) z := by
  simp only [paddedGram, Matrix.of_apply]
  split_ifs
  · simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact DifferentiableAt.fun_sum fun r _ => (hZ p r).mul (hY q r)
  · exact differentiableAt_const _

theorem differentiableAt_gram (hZ : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z)
    (hY : ∀ p q, DifferentiableAt ℂ (fun w => Y w p q) z) (i : ℕ) :
    DifferentiableAt ℂ (fun w => gram i (Z w) (Y w)) z :=
  differentiableAt_det (differentiableAt_paddedGram hZ hY i)

theorem differentiableAt_gramColumn (hZ : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z)
    (hY : ∀ p q, DifferentiableAt ℂ (fun w => Y w p q) z) (i j : Fin n) :
    DifferentiableAt ℂ (fun w => gramColumn i j (Z w) (Y w)) z := by
  refine differentiableAt_det fun p q => ?_
  simp only [Matrix.updateCol_apply, GramFormula.gramColumnVector]
  split_ifs
  · exact hZ p j
  · exact differentiableAt_const _
  · exact differentiableAt_paddedGram hZ hY i p q

theorem differentiableAt_hatCoord (hZ : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z)
    (hY : ∀ p q, DifferentiableAt ℂ (fun w => Y w p q) z)
    (hpos : ∀ l : ℕ, l ≤ n → 0 < (gram l (Z z) (Y z)).re) (i j : Fin n) :
    DifferentiableAt ℂ (fun w => hatCoord i j (Z w) (Y w)) z := by
  have hG : ∀ (l : ℕ) (c : ℂ), l ≤ n → DifferentiableAt ℂ (fun w => gram l (Z w) (Y w) ^ c) z :=
    fun l c hl => (differentiableAt_gram hZ hY l).cpow_const
      (mem_slitPlane_of_re_pos (hpos l hl))
  unfold hatCoord
  exact ((differentiableAt_gramColumn hZ hY i j).mul (hG i _ i.isLt.le)).mul
    (hG (i + 1) _ i.isLt)

/-- A polarized Gram expression is complex differentiable along a pair of curves with
differentiable entries at a point where all polarized Gram determinants have positive real
part. -/
theorem differentiableAt_gramExpression (s : Fin n → ℂ)
    (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ)
    (hZ : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z)
    (hY : ∀ p q, DifferentiableAt ℂ (fun w => Y w p q) z)
    (hpos : ∀ l : ℕ, l ≤ n → 0 < (gram l (Z z) (Y z)).re) :
    DifferentiableAt ℂ (fun w => gramExpression s P (Z w) (Y w)) z := by
  have hG : ∀ (l : ℕ) (c : ℂ), l ≤ n → DifferentiableAt ℂ (fun w => gram l (Z w) (Y w) ^ c) z :=
    fun l c hl => (differentiableAt_gram hZ hY l).cpow_const
      (mem_slitPlane_of_re_pos (hpos l hl))
  have hpos' : ∀ l : ℕ, l ≤ n → 0 < (gram l (Y z) (Z z)).re := fun l hl => by
    rw [gram_swap]
    exact hpos l hl
  unfold gramExpression
  refine (differentiableAt_finset_prod _ fun (l : Fin n) _ =>
    (hG (l : ℕ) _ l.isLt.le).mul (hG ((l : ℕ) + 1) _ l.isLt)).mul ?_
  refine differentiableAt_mvPolynomial_eval P fun v => ?_
  cases v with
  | inl ij => exact differentiableAt_hatCoord hZ hY hpos ij.1 ij.2
  | inr ij => exact differentiableAt_hatCoord hY hZ hpos' ij.1 ij.2

end Differentiable

/-! ## Continuity of polarized Gram expressions -/

section Continuous

variable {X : Type*} [TopologicalSpace X] {Z Y : X → Matrix (Fin n) (Fin n) ℂ}

theorem continuous_paddedGram (hZ : Continuous Z) (hY : Continuous Y) (i : ℕ) :
    Continuous fun x => paddedGram i (Z x) (Y x) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [paddedGram, Matrix.of_apply]
  split_ifs
  · simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact continuous_finsetSum _ fun r _ =>
      ((continuous_apply r).comp ((continuous_apply p).comp hZ)).mul
        ((continuous_apply r).comp ((continuous_apply q).comp hY))
  · exact continuous_const

theorem continuous_gram (hZ : Continuous Z) (hY : Continuous Y) (i : ℕ) :
    Continuous fun x => gram i (Z x) (Y x) :=
  (continuous_paddedGram hZ hY i).matrix_det

theorem continuous_gramColumn (hZ : Continuous Z) (hY : Continuous Y) (i j : Fin n) :
    Continuous fun x => gramColumn i j (Z x) (Y x) := by
  refine Continuous.matrix_det (continuous_pi fun p => continuous_pi fun q => ?_)
  simp only [Matrix.updateCol_apply, GramFormula.gramColumnVector]
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply p).comp hZ)
  · exact continuous_const
  · exact (continuous_apply q).comp ((continuous_apply p).comp (continuous_paddedGram hZ hY i))

theorem continuousAt_hatCoord (hZ : Continuous Z) (hY : Continuous Y) {x : X}
    (hpos : ∀ l : ℕ, l ≤ n → 0 < (gram l (Z x) (Y x)).re) (i j : Fin n) :
    ContinuousAt (fun y => hatCoord i j (Z y) (Y y)) x := by
  have hG : ∀ (l : ℕ) (c : ℂ), l ≤ n → ContinuousAt (fun y => gram l (Z y) (Y y) ^ c) x :=
    fun l c hl => ((continuous_gram hZ hY l).continuousAt).cpow continuousAt_const
      (mem_slitPlane_of_re_pos (hpos l hl))
  unfold hatCoord
  exact (((continuous_gramColumn hZ hY i j).continuousAt).mul (hG i _ i.isLt.le)).mul
    (hG (i + 1) _ i.isLt)

/-- A polarized Gram expression is continuous along continuous families of matrices at the
points where all polarized Gram determinants have positive real part. -/
theorem continuousAt_gramExpression (s : Fin n → ℂ)
    (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ)
    (hZ : Continuous Z) (hY : Continuous Y) {x : X}
    (hpos : ∀ l : ℕ, l ≤ n → 0 < (gram l (Z x) (Y x)).re) :
    ContinuousAt (fun y => gramExpression s P (Z y) (Y y)) x := by
  have hG : ∀ (l : ℕ) (c : ℂ), l ≤ n → ContinuousAt (fun y => gram l (Z y) (Y y) ^ c) x :=
    fun l c hl => ((continuous_gram hZ hY l).continuousAt).cpow continuousAt_const
      (mem_slitPlane_of_re_pos (hpos l hl))
  have hpos' : ∀ l : ℕ, l ≤ n → 0 < (gram l (Y x) (Z x)).re := fun l hl => by
    rw [gram_swap]
    exact hpos l hl
  unfold gramExpression
  refine (tendsto_finsetProd _ fun (l : Fin n) _ =>
    (hG (l : ℕ) _ l.isLt.le).mul (hG ((l : ℕ) + 1) _ l.isLt)).mul ?_
  have hv : ContinuousAt (fun y => Sum.elim
      (fun ij : Fin n × Fin n => hatCoord ij.1 ij.2 (Z y) (Y y))
      (fun ij : Fin n × Fin n => hatCoord ij.1 ij.2 (Y y) (Z y))) x := by
    refine continuousAt_pi.mpr fun v => ?_
    cases v with
    | inl ij => exact continuousAt_hatCoord hZ hY hpos ij.1 ij.2
    | inr ij => exact continuousAt_hatCoord hY hZ hpos' ij.1 ij.2
  exact (MvPolynomial.continuous_eval P).continuousAt.comp hv

end Continuous

/-! ## Real diagonal one-parameter subgroups of `GL_n(ℂ)` -/

/-- The diagonal one-parameter subgroup `t ↦ diag(e^(t h_0), …, e^(t h_(n-1)))` of `GL_n(ℂ)`,
for real `h`. -/
def expDiag (h : Fin n → ℝ) (t : ℝ) : Langlands.GeneralLinear n ℂ :=
  Iwasawa.diagonalUnits fun j =>
    Units.mk0 ((Real.exp (t * h j) : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos _).ne')

theorem expDiag_val (h : Fin n → ℝ) (t : ℝ) :
    ((expDiag h t : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal fun j => ((Real.exp (t * h j) : ℝ) : ℂ) :=
  rfl

theorem expDiag_add (h : Fin n → ℝ) (s t : ℝ) :
    expDiag h (s + t) = expDiag h s * expDiag h t := by
  apply Units.ext
  rw [Units.val_mul, expDiag_val, expDiag_val, expDiag_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  rw [add_mul, Real.exp_add, Complex.ofReal_mul]

theorem expDiag_zero (h : Fin n → ℝ) : expDiag h 0 = 1 := by
  apply Units.ext
  rw [expDiag_val]
  simp

/-- The derivative at `0` of `s ↦ f(p · exp(s H))`, `H = diag(h)`, is `(R(H) f)(p)`. -/
theorem hasDerivAt_mul_expDiag {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (p : Langlands.GeneralLinear n ℂ)
    (h : Fin n → ℝ) :
    HasDerivAt (fun s => f (p * expDiag h s))
      (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) f p) 0 := by
  have hγ : ∀ i j, HasDerivAt
      (fun s => ((expDiag h s : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) i j) (Matrix.diagonal (fun j => (h j : ℂ)) i j) 0 := by
    intro i j
    simp only [expDiag_val, Matrix.diagonal_apply]
    split_ifs with hij
    · have := (((hasDerivAt_id (0 : ℝ)).mul_const (h i)).exp).ofReal_comp
      simpa using this
    · exact hasDerivAt_const _ _
  have hc : HasDerivAt (fun s => (p : Matrix (Fin n) (Fin n) ℂ) *
      ((expDiag h s : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ))
      ((p : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal fun j => (h j : ℂ)) 0 :=
    (hasDerivAt_matrix_of_entries hγ).const_mul (p : Matrix (Fin n) (Fin n) ℂ)
  have hc0 : (p : Matrix (Fin n) (Fin n) ℂ) *
      ((expDiag h 0 : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        (p : Matrix (Fin n) (Fin n) ℂ) := by
    rw [expDiag_zero, Units.val_one, mul_one]
  have hd : HasFDerivAt (unitsExtension f)
      (fderiv ℝ (unitsExtension f) (p : Matrix (Fin n) (Fin n) ℂ))
      ((p : Matrix (Fin n) (Fin n) ℂ) *
        ((expDiag h 0 : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hc0]
    exact (differentiableAt_unitsExtension hf (Units.isUnit p)).hasFDerivAt
  have hfun : (fun s => f (p * expDiag h s)) = unitsExtension f ∘ fun s =>
      (p : Matrix (Fin n) (Fin n) ℂ) *
        ((expDiag h s : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    funext s
    rw [Function.comp_apply, ← unitsExtension_val f (p * expDiag h s), Units.val_mul]
  rw [hfun, rightDerivative_eq_fderiv hf]
  exact hd.comp_hasDerivAt (0 : ℝ) hc

/-- The derivative at `t` of `s ↦ f(x · exp(s H))` is `(R(H) f)(x · exp(t H))`. -/
theorem hasDerivAt_mul_expDiag_at {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (x : Langlands.GeneralLinear n ℂ)
    (h : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => f (x * expDiag h s))
      (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) f
        (x * expDiag h t)) t := by
  have h0 : HasDerivAt (fun s => f (x * expDiag h t * expDiag h s))
      (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) f
        (x * expDiag h t)) (t - t) := by
    rw [sub_self]
    exact hasDerivAt_mul_expDiag hf _ h
  convert HasDerivAt.comp_sub_const t t h0 using 1
  funext s
  rw [mul_assoc, ← expDiag_add, add_sub_cancel]

/-! ## Polarized complexified curves -/

/-- The first curve `z ↦ κ g diag(e^(z h_0), …, e^(z h_(n-1)))`, for `κ ∈ U(n)`. -/
def zCurve (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (z : ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((κ : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)) *
    Matrix.diagonal fun j => Complex.exp (z * h j)

/-- The second curve `z ↦ conj(κ g) diag(e^(z h_0), …, e^(z h_(n-1)))`; at real `z` it is the
complex conjugate of the first. -/
def yCurve (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (z : ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((κ : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)).map (starRingEnd ℂ) *
    Matrix.diagonal fun j => Complex.exp (z * h j)

theorem zCurve_apply (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (z : ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (p q : Fin n) :
    zCurve g h z κ p q =
      ((κ : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)) p q *
        Complex.exp (z * h q) := by
  rw [zCurve, Matrix.mul_diagonal]

theorem yCurve_apply (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (z : ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (p q : Fin n) :
    yCurve g h z κ p q =
      conj (((κ : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)) p q) *
        Complex.exp (z * h q) := by
  rw [yCurve, Matrix.mul_diagonal, Matrix.map_apply]

theorem zCurve_ofReal (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (t : ℝ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    zCurve g h t κ = ((Unitary.toUnits κ * g * expDiag h t : Langlands.GeneralLinear n ℂ) :
      Matrix (Fin n) (Fin n) ℂ) := by
  ext p q
  rw [zCurve_apply, Units.val_mul, Units.val_mul, expDiag_val, Matrix.mul_diagonal]
  push_cast
  rfl

theorem yCurve_ofReal (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (t : ℝ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    yCurve g h t κ = ((Unitary.toUnits κ * g * expDiag h t : Langlands.GeneralLinear n ℂ) :
      Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) := by
  ext p q
  rw [yCurve_apply, Matrix.map_apply, Units.val_mul, Units.val_mul, expDiag_val,
    Matrix.mul_diagonal, map_mul, Complex.conj_ofReal, Complex.ofReal_exp]
  push_cast
  rfl

theorem continuous_zCurve (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) :
    Continuous fun x : ℂ × Matrix.unitaryGroup (Fin n) ℂ => zCurve g h x.1 x.2 := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [zCurve_apply]
  have hm : Continuous fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      (κ : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.matrix_mul continuous_const
  refine Continuous.mul ?_ ?_
  · exact ((continuous_apply q).comp ((continuous_apply p).comp hm)).comp continuous_snd
  · exact Complex.continuous_exp.comp (continuous_fst.mul continuous_const)

theorem continuous_yCurve (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) :
    Continuous fun x : ℂ × Matrix.unitaryGroup (Fin n) ℂ => yCurve g h x.1 x.2 := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [yCurve_apply]
  have hm : Continuous fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      (κ : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.matrix_mul continuous_const
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_conj.comp
      (((continuous_apply q).comp ((continuous_apply p).comp hm)).comp continuous_snd)
  · exact Complex.continuous_exp.comp (continuous_fst.mul continuous_const)

theorem differentiableAt_zCurve (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (z : ℂ) (p q : Fin n) :
    DifferentiableAt ℂ (fun w => zCurve g h w κ p q) z := by
  simp only [zCurve_apply]
  exact (differentiableAt_const _).mul ((differentiableAt_id.mul_const _).cexp)

theorem differentiableAt_yCurve (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (z : ℂ) (p q : Fin n) :
    DifferentiableAt ℂ (fun w => yCurve g h w κ p q) z := by
  simp only [yCurve_apply]
  exact (differentiableAt_const _).mul ((differentiableAt_id.mul_const _).cexp)

/-- The polarized Gram determinants of an invertible complex matrix and its conjugate are
positive. -/
theorem gram_conj_re_pos (x : Langlands.GeneralLinear n ℂ) (i : ℕ) :
    0 < (gram i (x : Matrix (Fin n) (Fin n) ℂ)
      ((x : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))).re := by
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
  have hd : ∀ l, (Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) l l ≠ 0 := fun l => by
    rw [diagonal_mul_apply_self]
    exact (a l).ne_zero
  change 0 < (gram i ((Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) *
        (k : Matrix (Fin n) (Fin n) ℂ)) (((Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) *
        (k : Matrix (Fin n) (Fin n) ℂ)).map (starRingEnd ℂ))).re
  rw [gram_mul_conj (isUpperTriangular_diagonal_mul a u) (mul_conj_transpose_eq_one_of_mem hk),
    Complex.ofReal_re]
  exact pow_pos (norm_pos_iff.mpr (diagonalTail_ne_zero' hd i)) 2

theorem gram_curve_ofReal_re_pos (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ)
    (t : ℝ) (κ : Matrix.unitaryGroup (Fin n) ℂ) (l : ℕ) :
    0 < (gram l (zCurve g h t κ) (yCurve g h t κ)).re := by
  rw [zCurve_ofReal, yCurve_ofReal]
  exact gram_conj_re_pos _ l

/-- The pairs `(z, κ)` at which all polarized Gram determinants of the curves have positive
real part. -/
def goodSet (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) :
    Set (ℂ × Matrix.unitaryGroup (Fin n) ℂ) :=
  ⋂ l : Fin (n + 1), {x | 0 < (gram (l : ℕ) (zCurve g h x.1 x.2) (yCurve g h x.1 x.2)).re}

theorem isOpen_goodSet (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) :
    IsOpen (goodSet g h) :=
  isOpen_iInter_of_finite fun l => isOpen_lt continuous_const
    (Complex.continuous_re.comp
      (continuous_gram (continuous_zCurve g h) (continuous_yCurve g h) l))

theorem mem_goodSet_iff {g : Langlands.GeneralLinear n ℂ} {h : Fin n → ℝ}
    {x : ℂ × Matrix.unitaryGroup (Fin n) ℂ} :
    x ∈ goodSet g h ↔
      ∀ l : ℕ, l ≤ n → 0 < (gram l (zCurve g h x.1 x.2) (yCurve g h x.1 x.2)).re := by
  simp only [goodSet, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨fun H l hl => H ⟨l, Nat.lt_succ_of_le hl⟩, fun H l => H l (Nat.lt_succ_iff.mp l.isLt)⟩

/-- The integrand `gramExpression s P (κ g e^(zH)) (conj(κ g) e^(zH)) · φ(κ)` of the
complexified matrix coefficient. -/
def gramIntegrand (s : Fin n → ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ)
    (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ)
    (z : ℂ) (κ : Matrix.unitaryGroup (Fin n) ℂ) : ℂ :=
  gramExpression s P (zCurve g h z κ) (yCurve g h z κ) * φ κ

theorem differentiableAt_gramIntegrand (s : Fin n → ℂ)
    (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ)
    (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ)
    {z : ℂ} {κ : Matrix.unitaryGroup (Fin n) ℂ} (hx : (z, κ) ∈ goodSet g h) :
    DifferentiableAt ℂ (fun w => gramIntegrand s P g h φ w κ) z := by
  have hpos := (mem_goodSet_iff (x := (z, κ))).mp hx
  have hD := differentiableAt_gramExpression s P (Z := fun w => zCurve g h w κ)
    (Y := fun w => yCurve g h w κ) (fun p q => differentiableAt_zCurve g h κ z p q)
    (fun p q => differentiableAt_yCurve g h κ z p q) hpos
  exact hD.mul_const (φ κ)

theorem continuousAt_gramIntegrand (s : Fin n → ℂ)
    (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ)
    (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hφ : Continuous φ) {x : ℂ × Matrix.unitaryGroup (Fin n) ℂ} (hx : x ∈ goodSet g h) :
    ContinuousAt (Function.uncurry (gramIntegrand s P g h φ)) x := by
  have hpos := (mem_goodSet_iff (x := x)).mp hx
  have hC := continuousAt_gramExpression s P (continuous_zCurve g h) (continuous_yCurve g h) hpos
  exact hC.mul (hφ.comp continuous_snd).continuousAt

/-- Near every real point the curves stay in `goodSet` for all `κ`. -/
theorem exists_closedBall_subset_goodSet (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ)
    (t₀ : ℝ) : ∃ R > 0, ∀ z ∈ closedBall (t₀ : ℂ) R, ∀ κ, (z, κ) ∈ goodSet g h := by
  have hgood : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ, ((t₀ : ℂ), κ) ∈ goodSet g h := fun κ =>
    mem_goodSet_iff.mpr fun l _ => gram_curve_ofReal_re_pos g h t₀ κ l
  have hev : ∀ᶠ z in 𝓝 (t₀ : ℂ), ∀ κ ∈ (Set.univ : Set (Matrix.unitaryGroup (Fin n) ℂ)),
      (z, κ) ∈ goodSet g h :=
    isCompact_univ.eventually_forall_of_forall_eventually fun κ _ =>
      (isOpen_goodSet g h).mem_nhds (hgood κ)
  obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨ε / 2, half_pos hε, fun z hz κ =>
    hεU (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hε)) κ (Set.mem_univ κ)⟩

/-! ## Matrix coefficients along real diagonal one-parameter subgroups -/

section MatrixCoefficient

variable (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure μ]

/-- The `U(n)`-integral matrix coefficient `g ↦ ∫ f(κ g) φ(κ) dμ(κ)`. -/
def matrixCoefficient (f : Langlands.GeneralLinear n ℂ → ℂ)
    (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  ∫ κ, f (Unitary.toUnits κ * g) * φ κ ∂μ

/-- **Analyticity.** For a `U(n)`-finite function `f` of a principal series of `GL_n(ℂ)` and a
continuous `φ` on `U(n)`, the matrix coefficient `t ↦ ∫ f(κ g exp(tH)) φ(κ) dμ(κ)` along a real
diagonal one-parameter subgroup is real analytic, with derivative the matrix coefficient of
`R(H) f`. -/
theorem analyticAt_matrixCoefficient {χ : ℕ → ℂˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hφ : Continuous φ)
    (g : Langlands.GeneralLinear n ℂ) (h : Fin n → ℝ) (t₀ : ℝ) :
    AnalyticAt ℝ (fun t => matrixCoefficient μ f φ (g * expDiag h t)) t₀ ∧
      HasDerivAt (fun t => matrixCoefficient μ f φ (g * expDiag h t))
        (matrixCoefficient μ
          (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) f) φ
          (g * expDiag h t₀)) t₀ := by
  obtain ⟨P, hP⟩ := exists_gramExpression_eq e hχ hf
  have hsmooth := (Submodule.mem_inf.mp hf).1.1
  let F : ℂ → Matrix.unitaryGroup (Fin n) ℂ → ℂ :=
    gramIntegrand (GramFormula.shiftedExponent n e) P g h φ
  have hFreal : ∀ (t : ℝ) κ, F t κ = f (Unitary.toUnits κ * (g * expDiag h t)) * φ κ := by
    intro t κ
    simp only [F, gramIntegrand]
    rw [zCurve_ofReal, yCurve_ofReal, ← hP, mul_assoc]
  obtain ⟨R, hR, hball⟩ := exists_closedBall_subset_goodSet g h t₀
  have hc : ContinuousOn (Function.uncurry F) (closedBall (t₀ : ℂ) R ×ˢ Set.univ) := by
    rintro ⟨z, κ⟩ ⟨hz, -⟩
    exact (continuousAt_gramIntegrand (GramFormula.shiftedExponent n e) P g h hφ
      (hball z hz κ)).continuousWithinAt
  have hd : ∀ κ, DifferentiableOn ℂ (fun z => F z κ) (ball (t₀ : ℂ) R) := fun κ z hz =>
    (differentiableAt_gramIntegrand (GramFormula.shiftedExponent n e) P g h φ
      (hball z (ball_subset_closedBall hz) κ)).differentiableWithinAt
  have hΨ : (fun t : ℝ => ∫ κ, F t κ ∂μ) =
      fun t => matrixCoefficient μ f φ (g * expDiag h t) := by
    funext t
    simp only [matrixCoefficient]
    exact integral_congr_ae (ae_of_all _ fun κ => hFreal t κ)
  constructor
  · rw [← hΨ]
    exact analyticAt_comp_ofReal (analyticAt_integral_of_holomorphic μ hR hc hd)
  · have hD := (hasDerivAt_integral_of_holomorphic μ hR hc hd).comp_ofReal
    rw [hΨ] at hD
    convert hD using 1
    simp only [matrixCoefficient]
    refine integral_congr_ae (ae_of_all _ fun κ => ?_)
    have h1 : HasDerivAt (fun z => F z κ) (deriv (fun z => F z κ) (t₀ : ℂ)) (t₀ : ℂ) :=
      ((hd κ).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).hasDerivAt
    have h3 : HasDerivAt (fun y : ℝ => F y κ)
        (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) f
          (Unitary.toUnits κ * (g * expDiag h t₀)) * φ κ) t₀ := by
      have := (hasDerivAt_mul_expDiag_at hsmooth (Unitary.toUnits κ * g) h t₀).mul_const
        (φ κ)
      simp only [mul_assoc] at this
      convert this using 1
      funext y
      rw [hFreal]
    exact (h1.comp_ofReal.unique h3).symm

/-- **One-parameter vanishing.** Let `W` be a space of `U(n)`-finite functions of a principal
series of `GL_n(ℂ)`, stable under `R(H)` for `H = diag(h)` real. If `∫ w(κ g) φ(κ) dμ(κ) = 0` for
all `w ∈ W`, then `∫ w(κ g exp(tH)) φ(κ) dμ(κ) = 0` for all `w ∈ W` and all real `t`. -/
theorem matrixCoefficient_mul_expDiag_eq_zero {χ : ℕ → ℂˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l)
    {W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)}
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) (h : Fin n → ℝ)
    (hWD : ∀ w ∈ W,
      rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) w ∈ W)
    {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hφ : Continuous φ)
    (g : Langlands.GeneralLinear n ℂ) (h0 : ∀ w ∈ W, matrixCoefficient μ w φ g = 0) :
    ∀ w ∈ W, ∀ t : ℝ, matrixCoefficient μ w φ (g * expDiag h t) = 0 := by
  have hderiv : ∀ w ∈ W, deriv (fun t => matrixCoefficient μ w φ (g * expDiag h t)) =
      fun t => matrixCoefficient μ
        (rightDerivative (matrixModel ℂ n) (Matrix.diagonal fun j => (h j : ℂ)) w) φ
        (g * expDiag h t) := fun w hw => funext fun t =>
    (analyticAt_matrixCoefficient μ e hχ (hW hw) hφ g h t).2.deriv
  have hiter : ∀ j : ℕ, ∀ w ∈ W,
      iteratedDeriv j (fun t => matrixCoefficient μ w φ (g * expDiag h t)) 0 = 0 := by
    intro j
    induction j with
    | zero =>
      intro w hw
      rw [iteratedDeriv_zero, expDiag_zero, mul_one]
      exact h0 w hw
    | succ j ih =>
      intro w hw
      rw [iteratedDeriv_succ', hderiv w hw]
      exact ih _ (hWD w hw)
  intro w hw t
  have := eq_zero_of_iteratedDeriv_eq_zero
    (fun t _ => (analyticAt_matrixCoefficient μ e hχ (hW hw) hφ g h t).1) (hiter · w hw)
  exact congrFun this t

end MatrixCoefficient

/-! ## The `KAK` decomposition of `GL_n(ℂ)` -/

theorem star_diagonal_ofReal {d : Fin n → ℝ} :
    star (Matrix.diagonal fun i => (d i : ℂ)) = Matrix.diagonal fun i => (d i : ℂ) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- **`KAK` decomposition.** Every `g ∈ GL_n(ℂ)` is `k₁ · exp(H) · k₂` with `k₁, k₂ ∈ U(n)` and
`H` real diagonal. -/
theorem exists_kak (g : Langlands.GeneralLinear n ℂ) :
    ∃ k₁ ∈ unitaryCompact ℂ n, ∃ k₂ ∈ unitaryCompact ℂ n, ∃ h : Fin n → ℝ,
      g = k₁ * expDiag h 1 * k₂ := by
  classical
  set G : Matrix (Fin n) (Fin n) ℂ := (g : Matrix (Fin n) (Fin n) ℂ) with hGdef
  have hinj : Function.Injective G.mulVec := by
    intro x y hxy
    have := congrArg (fun v => ((g⁻¹ : Langlands.GeneralLinear n ℂ) :
      Matrix (Fin n) (Fin n) ℂ) *ᵥ v) hxy
    simpa [G, Matrix.mulVec_mulVec] using this
  have hA : (Gᴴ * G).PosDef := Matrix.PosDef.conjTranspose_mul_self G hinj
  set U : Matrix.unitaryGroup (Fin n) ℂ := hA.isHermitian.eigenvectorUnitary with hUdef
  set lam : Fin n → ℝ := hA.isHermitian.eigenvalues with hlamdef
  have hlam : ∀ i, 0 < lam i := hA.eigenvalues_pos
  have hD : star (U : Matrix (Fin n) (Fin n) ℂ) * (Gᴴ * G) * (U : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal fun i => (lam i : ℂ) := by
    have := hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [this]
    congr 1
  set sq : Fin n → ℝ := fun i => Real.sqrt (lam i) with hsqdef
  have hsq : ∀ i, 0 < sq i := fun i => Real.sqrt_pos.mpr (hlam i)
  let sU : Fin n → ℂˣ := fun i => Units.mk0 (sq i : ℂ) (by exact_mod_cast (hsq i).ne')
  let k₁ : Langlands.GeneralLinear n ℂ :=
    g * Unitary.toUnits U * Iwasawa.diagonalUnits sU⁻¹
  have hk₁val : (k₁ : Matrix (Fin n) (Fin n) ℂ) =
      G * (U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal fun i => (((sq i)⁻¹ : ℝ) : ℂ) := by
    simp only [k₁, Units.val_mul]
    congr 1
    change Matrix.diagonal (fun i => (((sU i)⁻¹ : ℂˣ) : ℂ)) = _
    congr 1
    funext i
    simp [sU]
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hk₁ : k₁ ∈ unitaryCompact ℂ n := by
    change (k₁ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [Matrix.mem_unitaryGroup_iff', hk₁val, star_mul, star_mul, star_diagonal_ofReal]
    have hG : star G = Gᴴ := rfl
    calc Matrix.diagonal (fun i => (((sq i)⁻¹ : ℝ) : ℂ)) *
          (star (U : Matrix (Fin n) (Fin n) ℂ) * star G) *
          (G * (U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal fun i => (((sq i)⁻¹ : ℝ) : ℂ))
        = Matrix.diagonal (fun i => (((sq i)⁻¹ : ℝ) : ℂ)) *
            (star (U : Matrix (Fin n) (Fin n) ℂ) * (Gᴴ * G) * (U : Matrix (Fin n) (Fin n) ℂ)) *
              Matrix.diagonal (fun i => (((sq i)⁻¹ : ℝ) : ℂ)) := by
          rw [hG]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext i
          have h2 : sq i * sq i = lam i := Real.mul_self_sqrt (hlam i).le
          rw [← h2]
          have hs : (sq i : ℂ) ≠ 0 := by exact_mod_cast (hsq i).ne'
          push_cast
          field_simp
  have hk₂ : Unitary.toUnits (star U) ∈ unitaryCompact ℂ n := (star U).2
  refine ⟨k₁, hk₁, Unitary.toUnits (star U), hk₂, fun i => Real.log (sq i), ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hk₁val, expDiag_val]
  have hexp : (Matrix.diagonal fun j => ((Real.exp (1 * Real.log (sq j)) : ℝ) : ℂ)) =
      Matrix.diagonal fun j => (sq j : ℂ) := by
    congr 1
    funext j
    rw [one_mul, Real.exp_log (hsq j)]
  rw [hexp]
  change G = G * (U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (fun i => (((sq i)⁻¹ : ℝ) : ℂ)) *
    Matrix.diagonal (fun j => (sq j : ℂ)) * star (U : Matrix (Fin n) (Fin n) ℂ)
  rw [Matrix.mul_assoc G, Matrix.mul_assoc G, Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℂ),
    Matrix.diagonal_mul_diagonal]
  have hone : (Matrix.diagonal fun i => (((sq i)⁻¹ : ℝ) : ℂ) * (sq i : ℂ)) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    have hs : (sq i : ℂ) ≠ 0 := by exact_mod_cast (hsq i).ne'
    push_cast
    exact inv_mul_cancel₀ hs
  rw [hone, Matrix.mul_one, Matrix.mul_assoc, hUU, Matrix.mul_one]

/-! ## Orthogonality invariance -/

section Invariance

variable (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem matrixCoefficient_mul_unitary (f : Langlands.GeneralLinear n ℂ → ℂ)
    (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ) (g k : Langlands.GeneralLinear n ℂ) :
    matrixCoefficient μ f φ (g * k) =
      matrixCoefficient μ (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k f) φ g := by
  simp only [matrixCoefficient]
  refine integral_congr_ae (ae_of_all _ fun κ => ?_)
  change f (Unitary.toUnits κ * (g * k)) * φ κ = f (Unitary.toUnits κ * g * k) * φ κ
  rw [mul_assoc]

/-- **Orthogonality invariance.** Let `W` be a subspace of the `U(n)`-finite functions of a
principal series of `GL_n(ℂ)` that is stable under right translation by `U(n)` and under the
right derivatives `R(X)`, `X ∈ 𝔤𝔩_n(ℂ)`, and let `φ` be continuous on `U(n)`. If
`∫ w(κ) φ(κ) dμ(κ) = 0` for all `w ∈ W`, then `∫ w(κ g) φ(κ) dμ(κ) = 0` for all `w ∈ W` and all
`g ∈ GL_n(ℂ)`. -/
theorem matrixCoefficient_eq_zero {χ : ℕ → ℂˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l)
    {W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)}
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hWK : ∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W)
    (hWD : ∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, rightDerivative (matrixModel ℂ n) X w ∈ W)
    {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hφ : Continuous φ)
    (h1 : ∀ w ∈ W, matrixCoefficient μ w φ 1 = 0) :
    ∀ w ∈ W, ∀ g, matrixCoefficient μ w φ g = 0 := by
  intro w hw g
  obtain ⟨k₁, hk₁, k₂, hk₂, h, rfl⟩ := exists_kak g
  rw [matrixCoefficient_mul_unitary]
  have hk1 : ∀ w ∈ W, matrixCoefficient μ w φ k₁ = 0 := fun w hw => by
    have := matrixCoefficient_mul_unitary μ w φ 1 k₁
    rw [one_mul] at this
    rw [this]
    exact h1 _ (hWK k₁ hk₁ w hw)
  exact matrixCoefficient_mul_expDiag_eq_zero μ e hχ hW h
    (fun w hw => hWD _ w hw) hφ k₁ hk1 _ (hWK k₂ hk₂ w hw) 1

end Invariance

end ComplexMatrixCoefficientAnalytic

open ComplexMatrixCoefficientAnalytic

/-- **Statement (orthogonality invariance for complex principal series).** Let `ds` be a list of
complex characters, `W` a subspace of the `U(n)`-finite functions of the smooth principal series
of the position characters of `ds` (the Library's `complexStandardModule n ds`), stable under
right translation by `U(n)` and under the right derivatives `R(X)`, `X ∈ 𝔤𝔩_n(ℂ)`. Let `μ` be a
finite measure on `U(n)` and `φ` a continuous function on `U(n)`. If `∫ w(κ) φ(κ) dμ(κ) = 0` for
every `w ∈ W`, then `∫ w(κ g) φ(κ) dμ(κ) = 0` for every `w ∈ W` and every `g ∈ GL_n(ℂ)`. -/
def ComplexPrincipalSeriesOrthogonalityInvarianceStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)),
    W ≤ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →
    (∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W) →
    (∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, rightDerivative (matrixModel ℂ n) X w ∈ W) →
    ∀ (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)), IsFiniteMeasure μ →
    ∀ (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ), Continuous φ →
      (∀ w ∈ W, ∫ κ, w (Unitary.toUnits κ) * φ κ ∂μ = 0) →
        ∀ w ∈ W, ∀ g : Langlands.GeneralLinear n ℂ,
          ∫ κ, w (Unitary.toUnits κ * g) * φ κ ∂μ = 0

theorem complexPrincipalSeriesOrthogonalityInvariance :
    ComplexPrincipalSeriesOrthogonalityInvarianceStatement := by
  intro n ds W hW hWK hWD μ _ φ hφ h1 w hw g
  have h1' : ∀ w ∈ W, ComplexMatrixCoefficientAnalytic.matrixCoefficient μ w φ 1 = 0 :=
    fun w hw => by
      simp only [ComplexMatrixCoefficientAnalytic.matrixCoefficient, mul_one]
      exact h1 w hw
  exact matrixCoefficient_eq_zero μ (ComplexGramFormula.complexPositionExponent ds)
    (ComplexGramFormula.complexPositionCharacter_eq_phaseUnit_mul ds) hW hWK hWD hφ h1' w hw g

end Langlands.Archimedean
