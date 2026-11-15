import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.ComplexMatrixCoefficientAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Extending `U(n)`-finite functions on `U(n)` to complex principal-series functions

Every continuous `U(n)`-finite function `φ` on `U(n)` with the phase equivariance forced by a
principal series of `GL_n(ℂ)` is the restriction of a `U(n)`-finite function of the smooth
principal series (`ComplexPrincipalSeriesExtension.extension_mem_kFiniteFunctions`). The extension
is explicit: `x ↦ ∏ₗ G_l(x, x̄)^(s_l) G_{l+1}(x, x̄)^(-s_l) · φ(κ̂(x))`, where `κ̂(x)` is the unitary
Iwasawa factor of `x` with positive diagonal in the triangular factor.
-/

noncomputable section

open Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace ComplexPrincipalSeriesExtension

open ComplexGramFormula

variable {n : ℕ}

/-! ## Phases and the unitary Iwasawa factor -/

theorem phaseUnit_mul (z w : ℂˣ) : phaseUnit (z * w) = phaseUnit z * phaseUnit w := by
  apply Units.ext
  simp only [phaseUnit_val, Units.val_mul, norm_mul, Complex.ofReal_mul]
  have hz : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero
  have hw : (‖(w : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr w.ne_zero
  field_simp

theorem phaseUnit_one : phaseUnit 1 = 1 := by
  apply Units.ext
  simp [phaseUnit_val]

/-- The diagonal matrix of phases `diag(aᵢ/|aᵢ|)`, as an element of `U(n)`. -/
def phaseMatrix (a : Fin n → ℂˣ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨Matrix.diagonal fun i => ((phaseUnit (a i) : ℂˣ) : ℂ), diagonalUnits_phaseUnit_mem a⟩

theorem phaseMatrix_val (a : Fin n → ℂˣ) :
    ((phaseMatrix a : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal fun i => ((phaseUnit (a i) : ℂˣ) : ℂ) := rfl

theorem phaseMatrix_mul (a a' : Fin n → ℂˣ) :
    phaseMatrix (fun i => a i * a' i) = phaseMatrix a * phaseMatrix a' := by
  apply Subtype.ext
  change (Matrix.diagonal fun i => ((phaseUnit (a i * a' i) : ℂˣ) : ℂ)) =
    Matrix.diagonal (fun i => ((phaseUnit (a i) : ℂˣ) : ℂ)) *
      Matrix.diagonal fun i => ((phaseUnit (a' i) : ℂˣ) : ℂ)
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [phaseUnit_mul, Units.val_mul]

theorem phaseMatrix_one : phaseMatrix (fun _ : Fin n => (1 : ℂˣ)) = 1 := by
  apply Subtype.ext
  change (Matrix.diagonal fun _ : Fin n => ((phaseUnit 1 : ℂˣ) : ℂ)) = 1
  rw [phaseUnit_one, Units.val_one, Matrix.diagonal_one]

/-- The unitary Iwasawa factor `κ̂(x)`, entries `hatCoord i j x x̄`. -/
def phaseOrth (x : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => hatCoord i j x (x.map (starRingEnd ℂ))

theorem phaseOrth_mul {b κ : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (hd : ∀ l, b l l ≠ 0) (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1) :
    phaseOrth (b * κ) = Matrix.diagonal (fun i => b i i / (‖b i i‖ : ℂ)) * κ := by
  ext i j
  rw [Matrix.diagonal_mul, phaseOrth, Matrix.of_apply, hatCoord_mul_conj hb hd hκ]

theorem val_iwasawa (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (k : Langlands.GeneralLinear n ℂ) :
    (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * (u : Langlands.GeneralLinear n ℂ) *
      k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (Matrix.diagonal (fun l => (a l : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) *
          (k : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem phaseOrth_iwasawa (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    phaseOrth (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) * k : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) =
      ((phaseMatrix a : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        (k : Matrix (Fin n) (Fin n) ℂ) := by
  have hd : ∀ l, (Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) l l ≠ 0 := fun l => by
    rw [diagonal_mul_apply_self]
    exact (a l).ne_zero
  rw [val_iwasawa, phaseOrth_mul (isUpperTriangular_diagonal_mul a u) hd
    (mul_conj_transpose_eq_one_of_mem hk), phaseMatrix_val]
  congr 2
  funext i
  rw [diagonal_mul_apply_self, phaseUnit_val]

theorem phaseOrth_mem (x : Langlands.GeneralLinear n ℂ) :
    phaseOrth (x : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
  rw [phaseOrth_iwasawa a u hk]
  exact Submonoid.mul_mem _ (phaseMatrix a).2 hk

/-- The unitary Iwasawa factor of `x ∈ GL_n(ℂ)` as an element of `U(n)`. -/
def phaseOrthPart (x : Langlands.GeneralLinear n ℂ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨phaseOrth (x : Matrix (Fin n) (Fin n) ℂ), phaseOrth_mem x⟩

theorem phaseOrthPart_iwasawa (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    phaseOrthPart ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) * k) =
      phaseMatrix a * ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ :=
  Subtype.ext (phaseOrth_iwasawa a u hk)

/-! ## The extension -/

variable (s : Fin n → ℂ)

/-- The extension of a function `φ` on `U(n)`:
`x ↦ ∏_l G_l(x, x̄)^(s_l) G_{l+1}(x, x̄)^(-s_l) · φ(κ̂(x))`. -/
def extension (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ) (x : Langlands.GeneralLinear n ℂ) : ℂ :=
  gramExpression s 1 (x : Matrix (Fin n) (Fin n) ℂ)
      ((x : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ)) * φ (phaseOrthPart x)

theorem extension_iwasawa (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ) (a : Fin n → ℂˣ)
    (u : upperUnipotent n ℂ) {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    extension s φ ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) * k) =
      (∏ l : Fin n, ((‖(a l : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s l) *
        φ (phaseMatrix a * ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩) := by
  have hd : ∀ l, (Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) l l ≠ 0 := fun l => by
    rw [diagonal_mul_apply_self]
    exact (a l).ne_zero
  unfold extension
  rw [phaseOrthPart_iwasawa a u hk, val_iwasawa,
    gramExpression_mul_conj (isUpperTriangular_diagonal_mul a u) hd
      (mul_conj_transpose_eq_one_of_mem hk), map_one, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [diagonal_mul_apply_self]

theorem iwasawa_unitary (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    Unitary.toUnits κ = (Iwasawa.diagonalUnits (fun _ : Fin n => (1 : ℂˣ)) :
      Langlands.GeneralLinear n ℂ) * ((1 : upperUnipotent n ℂ) : Langlands.GeneralLinear n ℂ) *
        Unitary.toUnits κ := by
  have h1 : (Iwasawa.diagonalUnits (fun _ : Fin n => (1 : ℂˣ)) : Langlands.GeneralLinear n ℂ) = 1 :=
    map_one _
  rw [h1, OneMemClass.coe_one, one_mul, one_mul]

theorem extension_unitary (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) : extension s φ (Unitary.toUnits κ) = φ κ := by
  have hκ : Unitary.toUnits κ ∈ unitaryCompact ℂ n := κ.2
  rw [iwasawa_unitary κ, extension_iwasawa s φ _ _ hκ, phaseMatrix_one, one_mul]
  simp only [Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow,
    Finset.prod_const_one, one_mul]
  rfl

theorem upperTriangular_mul_apply_self {A C : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) (i : Fin n) :
    (A * C) i i = A i i * C i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hC hij, mul_zero]

/-- The product `diag(a) u diag(a') u'` is `diag(a a') u''` for an upper unipotent `u''`. -/
theorem exists_iwasawa_mul (a a' : Fin n → ℂˣ) (u u' : upperUnipotent n ℂ) :
    ∃ u'' : upperUnipotent n ℂ,
      (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * (u : Langlands.GeneralLinear n ℂ) *
        ((Iwasawa.diagonalUnits a' : Langlands.GeneralLinear n ℂ) *
          (u' : Langlands.GeneralLinear n ℂ)) =
      (Iwasawa.diagonalUnits (fun i => a i * a' i) : Langlands.GeneralLinear n ℂ) *
        (u'' : Langlands.GeneralLinear n ℂ) := by
  set B : Langlands.GeneralLinear n ℂ :=
    (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * (u : Langlands.GeneralLinear n ℂ) *
      ((Iwasawa.diagonalUnits a' : Langlands.GeneralLinear n ℂ) * (u' : Langlands.GeneralLinear n ℂ))
    with hBdef
  set D : Langlands.GeneralLinear n ℂ :=
    (Iwasawa.diagonalUnits (fun i => a i * a' i) : Langlands.GeneralLinear n ℂ) with hDdef
  have hBup : (B : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular := by
    have : (B : Matrix (Fin n) (Fin n) ℂ) = (Matrix.diagonal (fun l => (a l : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) *
        (Matrix.diagonal (fun l => (a' l : ℂ)) *
          ((u' : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) := rfl
    rw [this]
    exact (isUpperTriangular_diagonal_mul a u).mul (isUpperTriangular_diagonal_mul a' u')
  have hBd : ∀ i, (B : Matrix (Fin n) (Fin n) ℂ) i i = (a i : ℂ) * a' i := fun i => by
    have : (B : Matrix (Fin n) (Fin n) ℂ) = (Matrix.diagonal (fun l => (a l : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) *
        (Matrix.diagonal (fun l => (a' l : ℂ)) *
          ((u' : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) := rfl
    rw [this, upperTriangular_mul_apply_self (isUpperTriangular_diagonal_mul a u)
      (isUpperTriangular_diagonal_mul a' u'), diagonal_mul_apply_self, diagonal_mul_apply_self]
  have hDinv : ((D⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal fun i => ((a i : ℂ) * a' i)⁻¹ := by
    rw [hDdef, ← map_inv, Iwasawa.diagonalUnits_val]
    congr 1
    funext i
    simp
  have hmem : D⁻¹ * B ∈ upperUnipotent n ℂ := by
    have hval : ((D⁻¹ * B : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun i => ((a i : ℂ) * a' i)⁻¹) * (B : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Units.val_mul, hDinv]
    refine ⟨?_, fun i => ?_⟩
    · change ((D⁻¹ * B : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ).BlockTriangular id
      rw [hval]
      exact (Matrix.blockTriangular_diagonal _).mul hBup
    · change ((D⁻¹ * B : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1
      rw [hval, Matrix.diagonal_mul, hBd]
      exact inv_mul_cancel₀ (mul_ne_zero (a i).ne_zero (a' i).ne_zero)
  exact ⟨⟨D⁻¹ * B, hmem⟩, by simp⟩

/-- **Equivariance.** -/
theorem extension_mul_left {χ : ℕ → ℂˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l)
    {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hφ : ∀ (a : Fin n → ℂˣ) (κ : Matrix.unitaryGroup (Fin n) ℂ),
      φ (phaseMatrix a * κ) =
        principalSeriesCharacter ℂ n χ (fun i => phaseUnit (a i)) * φ κ)
    (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    extension (GramFormula.shiftedExponent n e) φ
        ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
          (u : Langlands.GeneralLinear n ℂ) * g) =
      principalSeriesCharacter ℂ n χ a * extension (GramFormula.shiftedExponent n e) φ g := by
  obtain ⟨a', u', k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  obtain ⟨u'', hu''⟩ := exists_iwasawa_mul a a' u u'
  have hx : (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) *
        ((Iwasawa.diagonalUnits a' : Langlands.GeneralLinear n ℂ) *
          (u' : Langlands.GeneralLinear n ℂ) * k) =
      (Iwasawa.diagonalUnits (fun i => a i * a' i) : Langlands.GeneralLinear n ℂ) *
        (u'' : Langlands.GeneralLinear n ℂ) * k := by
    rw [← hu'']
    simp only [mul_assoc]
  rw [hx, extension_iwasawa _ φ _ _ hk, extension_iwasawa _ φ _ _ hk, phaseMatrix_mul, mul_assoc,
    hφ, ComplexGramFormula.principalSeriesCharacter_eq e hχ a]
  have hprod : (∏ l : Fin n, ((‖((a l * a' l : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ^
      GramFormula.shiftedExponent n e l) =
      (∏ l : Fin n, ((‖(a l : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ GramFormula.shiftedExponent n e l) *
        ∏ l : Fin n, ((‖(a' l : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ GramFormula.shiftedExponent n e l := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Units.val_mul, norm_mul, mul_pow, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _)]
  rw [hprod]
  ring

/-! ## Smoothness -/

section Smooth

variable {X Y : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}

theorem contDiff_paddedGram (hX : ∀ p q, ContDiff ℝ ∞ (fun y => X y p q))
    (hY : ∀ p q, ContDiff ℝ ∞ (fun y => Y y p q)) (l : ℕ) (p q : Fin n) :
    ContDiff ℝ ∞ (fun y => paddedGram l (X y) (Y y) p q) := by
  simp only [paddedGram, Matrix.of_apply]
  split_ifs
  · simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiff.sum fun r _ => (hX p r).mul (hY q r)
  · exact contDiff_const

theorem contDiff_gram (hX : ∀ p q, ContDiff ℝ ∞ (fun y => X y p q))
    (hY : ∀ p q, ContDiff ℝ ∞ (fun y => Y y p q)) (l : ℕ) :
    ContDiff ℝ ∞ (fun y => gram l (X y) (Y y)) :=
  contDiff_det_of_entries _ (contDiff_paddedGram hX hY l)

theorem contDiff_gramColumn (hX : ∀ p q, ContDiff ℝ ∞ (fun y => X y p q))
    (hY : ∀ p q, ContDiff ℝ ∞ (fun y => Y y p q)) (i j : Fin n) :
    ContDiff ℝ ∞ (fun y => gramColumn i j (X y) (Y y)) := by
  refine contDiff_det_of_entries _ fun p q => ?_
  simp only [Matrix.updateCol_apply, GramFormula.gramColumnVector]
  split_ifs
  · exact hX p j
  · exact contDiff_const
  · exact contDiff_paddedGram hX hY i p q

theorem contDiffAt_ofReal_cpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {y : E} (hf : ContDiffAt ℝ ∞ f y) (hpos : 0 < f y) (c : ℂ) :
    ContDiffAt ℝ ∞ (fun y => ((f y : ℝ) : ℂ) ^ c) y := by
  have hev : (fun y => ((f y : ℝ) : ℂ) ^ c) =ᶠ[𝓝 y]
      fun y => Complex.exp (((Real.log (f y) : ℝ) : ℂ) * c) := by
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hpos)] with z hz
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hz.ne'), ← Complex.ofReal_log hz.le]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf.log hpos.ne')).mul
    contDiffAt_const).cexp

theorem contDiffAt_mvPolynomial_eval {σ : Type*} (P : MvPolynomial σ ℂ)
    {v : σ → Matrix (Fin n) (Fin n) ℂ → ℂ} {y : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ s, ContDiffAt ℝ ∞ (v s) y) :
    ContDiffAt ℝ ∞ (fun y => MvPolynomial.eval (fun s => v s y) P) y := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact contDiffAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p s hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (h s)

/-- At an invertible matrix the polarized Gram determinants with the conjugate are positive real
numbers. -/
theorem gram_conj_eq_ofReal {y : Matrix (Fin n) (Fin n) ℂ} (hy : IsUnit y) (l : ℕ) :
    gram l y (y.map (starRingEnd ℂ)) = (((gram l y (y.map (starRingEnd ℂ))).re : ℝ) : ℂ) ∧
      0 < (gram l y (y.map (starRingEnd ℂ))).re := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨?_, ComplexMatrixCoefficientAnalytic.gram_conj_re_pos x l⟩
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
  rw [val_iwasawa, gram_mul_conj (isUpperTriangular_diagonal_mul a u)
    (mul_conj_transpose_eq_one_of_mem hk), Complex.ofReal_re]

/-- Polarized Gram expressions at `(y, ȳ)` are smooth on the invertible matrices. -/
theorem contDiffOn_gramExpression (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ContDiffOn ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      gramExpression s P y (y.map (starRingEnd ℂ))) {y | IsUnit y} := by
  intro y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have hX : ∀ p q, ContDiff ℝ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z p q) := contDiff_entry
  have hY : ∀ p q, ContDiff ℝ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ =>
      (z.map (starRingEnd ℂ)) p q) := contDiff_conj_entry
  have hopen := isOpen_setOf_isUnit_matrix (F := ℂ) (N := n)
  have hG : ∀ (l : ℕ) (c : ℂ), ContDiffAt ℝ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ =>
      gram l z (z.map (starRingEnd ℂ)) ^ c) y := by
    intro l c
    have hre : ContDiff ℝ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ =>
        (gram l z (z.map (starRingEnd ℂ))).re) :=
      Complex.reCLM.contDiff.comp (contDiff_gram hX hY l)
    have hev : (fun z : Matrix (Fin n) (Fin n) ℂ => gram l z (z.map (starRingEnd ℂ)) ^ c) =ᶠ[𝓝 y]
        fun z => (((gram l z (z.map (starRingEnd ℂ))).re : ℝ) : ℂ) ^ c := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [← (gram_conj_eq_ofReal hz l).1]
    exact (contDiffAt_ofReal_cpow hre.contDiffAt (gram_conj_eq_ofReal hy l).2 c).congr_of_eventuallyEq hev
  have hG' : ∀ (l : ℕ) (c : ℂ), ContDiffAt ℝ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ =>
      gram l (z.map (starRingEnd ℂ)) z ^ c) y := by
    intro l c
    have : (fun z : Matrix (Fin n) (Fin n) ℂ => gram l (z.map (starRingEnd ℂ)) z ^ c) =
        fun z => gram l z (z.map (starRingEnd ℂ)) ^ c := funext fun z => by rw [gram_swap]
    rw [this]
    exact hG l c
  unfold gramExpression
  refine (contDiffAt_prod fun (l : Fin n) _ => (hG (l : ℕ) _).mul (hG ((l : ℕ) + 1) _)).mul ?_
  refine contDiffAt_mvPolynomial_eval P fun v => ?_
  cases v with
  | inl ij =>
    unfold hatCoord
    exact (((contDiff_gramColumn hX hY ij.1 ij.2).contDiffAt).mul (hG _ _)).mul (hG _ _)
  | inr ij =>
    unfold hatCoord
    exact (((contDiff_gramColumn hY hX ij.1 ij.2).contDiffAt).mul (hG' _ _)).mul (hG' _ _)

end Smooth

theorem extension_eq_gramExpression {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    {P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ}
    (hP : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      φ κ = MvPolynomial.eval (UnitaryFinitePolynomial.coordValue κ) P)
    (x : Langlands.GeneralLinear n ℂ) :
    extension s φ x = gramExpression s P (x : Matrix (Fin n) (Fin n) ℂ)
      ((x : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ)) := by
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
  have hd : ∀ l, (Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) l l ≠ 0 := fun l => by
    rw [diagonal_mul_apply_self]
    exact (a l).ne_zero
  rw [extension_iwasawa s φ a u hk, val_iwasawa,
    gramExpression_mul_conj (isUpperTriangular_diagonal_mul a u) hd
      (mul_conj_transpose_eq_one_of_mem hk), hP]
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [diagonal_mul_apply_self]
  · refine congrArg (fun v => MvPolynomial.eval v P) (funext fun v => ?_)
    cases v with
    | inl ij =>
      change ((Matrix.diagonal fun i => ((phaseUnit (a i) : ℂˣ) : ℂ)) *
        (k : Matrix (Fin n) (Fin n) ℂ)) ij.1 ij.2 = _
      rw [Matrix.diagonal_mul]
      simp only [Sum.elim_inl, diagonal_mul_apply_self, phaseUnit_val]
    | inr ij =>
      change star (((Matrix.diagonal fun i => ((phaseUnit (a i) : ℂˣ) : ℂ)) *
        (k : Matrix (Fin n) (Fin n) ℂ)) ij.1 ij.2) = _
      rw [Matrix.diagonal_mul]
      simp only [Sum.elim_inr, diagonal_mul_apply_self, phaseUnit_val]
      rfl

theorem contMDiff_extension {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    {P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ}
    (hP : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      φ κ = MvPolynomial.eval (UnitaryFinitePolynomial.coordValue κ) P) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (extension s φ) :=
  contMDiff_of_contDiffOn (contDiffOn_gramExpression s P)
    fun g => extension_eq_gramExpression s hP g

/-! ## The extension lies in the principal series and is `U(n)`-finite -/

/-- The extension as a linear map. -/
def extensionLinear : (Matrix.unitaryGroup (Fin n) ℂ → ℂ) →ₗ[ℂ]
    (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun := extension s
  map_add' φ ψ := funext fun x => by
    simp only [extension, Pi.add_apply, mul_add]
  map_smul' c φ := funext fun x => by
    simp only [extension, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

variable {χ : ℕ → ℂˣ → ℂ} (e : ℕ → ℂ)
  (hχ : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l)

include hχ in
theorem extension_mem_principalSeries {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hφc : Continuous φ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => φ (x * k))))
    (hφM : ∀ (a : Fin n → ℂˣ) (κ : Matrix.unitaryGroup (Fin n) ℂ),
      φ (phaseMatrix a * κ) =
        principalSeriesCharacter ℂ n χ (fun i => phaseUnit (a i)) * φ κ) :
    extension (GramFormula.shiftedExponent n e) φ ∈ principalSeries ℂ n χ := by
  obtain ⟨P, hP⟩ := UnitaryFinitePolynomial.exists_mvPolynomial_of_finiteDimensional_span
    hφc hfin
  exact ⟨contMDiff_extension _ hP, extension_mul_left e hχ hφM⟩

theorem finiteDimensional_translate {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => φ (x * k))))
    (k₀ : Matrix.unitaryGroup (Fin n) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => φ (x * k * k₀))) := by
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x => φ (x * k * k₀)) ≤ Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
        fun x => φ (x * k)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k * k₀, funext fun x => by
      show φ (x * (k * k₀)) = φ (x * k * k₀)
      rw [mul_assoc]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem eq_of_eqOn_unitary {f g : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ principalSeries ℂ n χ) (hg : g ∈ principalSeries ℂ n χ)
    (h : ∀ k ∈ unitaryCompact ℂ n, f k = g k) : f = g := by
  have hsub := ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn
    (Submodule.sub_mem _ hf hg) (fun k hk => by simp [h k hk])
  exact sub_eq_zero.mp hsub

include hχ in
theorem rightTranslation_extension {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hφc : Continuous φ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => φ (x * k))))
    (hφM : ∀ (a : Fin n → ℂˣ) (κ : Matrix.unitaryGroup (Fin n) ℂ),
      φ (phaseMatrix a * κ) =
        principalSeriesCharacter ℂ n χ (fun i => phaseUnit (a i)) * φ κ)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (Unitary.toUnits k)
        (extension (GramFormula.shiftedExponent n e) φ) =
      extension (GramFormula.shiftedExponent n e) (fun κ => φ (κ * k)) := by
  have h₁ := rightTranslation_mem_principalSeries (χ := χ)
    (extension_mem_principalSeries e hχ hφc hfin hφM) (Unitary.toUnits k)
  have h₂ : extension (GramFormula.shiftedExponent n e) (fun κ => φ (κ * k)) ∈
      principalSeries ℂ n χ :=
    extension_mem_principalSeries e hχ (hφc.comp (continuous_id.mul continuous_const))
      (finiteDimensional_translate hfin k) fun a κ => by
        show φ (phaseMatrix a * κ * k) = _ * φ (κ * k)
        rw [mul_assoc, hφM]
  refine eq_of_eqOn_unitary h₁ h₂ fun g hg => ?_
  have hgu : g = Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℂ), hg⟩ :
      Matrix.unitaryGroup (Fin n) ℂ) := Units.ext rfl
  rw [hgu]
  change extension _ φ (Unitary.toUnits _ * Unitary.toUnits k) = _
  rw [← map_mul, extension_unitary, extension_unitary]

include hχ in
/-- **Extension.** -/
theorem extension_mem_kFiniteFunctions {φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hφc : Continuous φ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => φ (x * k))))
    (hφM : ∀ (a : Fin n → ℂˣ) (κ : Matrix.unitaryGroup (Fin n) ℂ),
      φ (phaseMatrix a * κ) =
        principalSeriesCharacter ℂ n χ (fun i => phaseUnit (a i)) * φ κ) :
    extension (GramFormula.shiftedExponent n e) φ ∈
      kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) := by
  refine Submodule.mem_inf.mpr ⟨extension_mem_principalSeries e hχ hφc hfin hφM, ?_⟩
  rw [mem_kFiniteVectors_iff]
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
        (extension (GramFormula.shiftedExponent n e) φ)) ≤
      (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
        fun x => φ (x * k))).map (extensionLinear (GramFormula.shiftedExponent n e)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have hk : (k : Langlands.GeneralLinear n ℂ) = Unitary.toUnits
        (⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ :
          Matrix.unitaryGroup (Fin n) ℂ) := Units.ext rfl
    simp only
    rw [hk, rightTranslation_extension e hχ hφc hfin hφM]
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end ComplexPrincipalSeriesExtension

open ComplexPrincipalSeriesExtension ComplexGramFormula

/-- **Statement (extension of `U(n)`-finite functions to complex principal series).** Let `ds` be
a list of complex characters and `φ : U(n) → ℂ` a continuous function whose right translates span
a finite-dimensional space and which satisfies
`φ(diag(a/|a|) κ) = principalSeriesCharacter ℂ n (complexPositionCharacter ds) (a/|a|) · φ(κ)` for
all `a ∈ (ℂˣ)ⁿ` and `κ ∈ U(n)`. Then `φ` is the restriction to `U(n)` of a `U(n)`-finite function
of `complexStandardModule n ds`. -/
def ComplexPrincipalSeriesExtensionStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ),
    Continuous φ →
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => φ (x * k))) →
    (∀ (a : Fin n → ℂˣ) (κ : Matrix.unitaryGroup (Fin n) ℂ),
      φ (phaseMatrix a * κ) =
        principalSeriesCharacter ℂ n (complexPositionCharacter ds)
          (fun i => phaseUnit (a i)) * φ κ) →
    ∃ f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      ∀ κ : Matrix.unitaryGroup (Fin n) ℂ, f (Unitary.toUnits κ) = φ κ

theorem complexPrincipalSeriesExtension : ComplexPrincipalSeriesExtensionStatement :=
  fun _ ds _ hφc hfin hφM =>
    ⟨_, extension_mem_kFiniteFunctions (complexPositionExponent ds)
      (complexPositionCharacter_eq_phaseUnit_mul ds) hφc hfin hφM, extension_unitary _ _⟩

end Langlands.Archimedean
