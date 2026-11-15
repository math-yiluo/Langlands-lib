import Langlands.Representation.Archimedean.PrincipalSeriesGramFormula
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Extending `O(n)`-finite functions on `O(n)` to principal-series functions
-/

noncomputable section

open Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace PrincipalSeriesExtension

open GramFormula

variable {n : ℕ}

/-! ## The signed orthogonal part -/

/-- The signed orthogonal part `κ̂(x)` of a real matrix: entries
`gramColumn i j x · (√G_i)⁻¹ (√G_{i+1})⁻¹`. For `x = b κ` it is `diag(sgn b_ii) κ`. -/
def signedOrthogonal (x : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => gramColumn i j x * (Real.sqrt (gram (i : ℕ) x))⁻¹ *
    (Real.sqrt (gram ((i : ℕ) + 1) x))⁻¹

theorem signedOrthogonal_mul {b κ : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    (hd : ∀ l, b l l ≠ 0) (hκ : κ * κᵀ = 1) :
    signedOrthogonal (b * κ) = Matrix.diagonal (fun i => signReal (b i i)) * κ := by
  ext i j
  rw [Matrix.diagonal_mul, signedOrthogonal, Matrix.of_apply, gramColumn_mul hb hκ,
    gram_mul hb hκ, gram_mul hb hκ, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    diagonalTail_succ b i, mul_mul_inv_abs (hd i) (diagonalTail_ne_zero hd _)]

/-- The diagonal sign matrix `diag(sgn a_i)` as an element of `O(n)`. -/
def signMatrix (a : Fin n → ℝˣ) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨Matrix.diagonal fun i => signReal (a i), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, star_trivial]
    unfold signReal
    split_ifs <;> norm_num⟩

theorem signedOrthogonal_mem (x : Langlands.GeneralLinear n ℝ) :
    signedOrthogonal (x : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.unitaryGroup (Fin n) ℝ := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
  have hd : ∀ l, (Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) l l ≠ 0 := fun l => by
    rw [diagonal_mul_apply_self]
    exact (a l).ne_zero
  change signedOrthogonal ((Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) *
        (k : Matrix (Fin n) (Fin n) ℝ)) ∈ _
  rw [signedOrthogonal_mul (isUpperTriangular_diagonal_mul a u) hd (mul_transpose_eq_one_of_mem hk)]
  have hsign : (Matrix.diagonal fun i => signReal ((Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) i i)) =
        ((signMatrix a : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
    change _ = Matrix.diagonal fun i => signReal (a i)
    congr 1
    funext i
    rw [diagonal_mul_apply_self]
  rw [hsign]
  exact Submonoid.mul_mem _ (signMatrix a).2 hk

/-- The signed orthogonal part of `x ∈ GL_n(ℝ)` as an element of `O(n)`. -/
def signedOrthogonalPart (x : Langlands.GeneralLinear n ℝ) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨signedOrthogonal (x : Matrix (Fin n) (Fin n) ℝ), signedOrthogonal_mem x⟩

/-- The diagonal sign matrix `diag(sgn d_i)` of real numbers, as an element of `O(n)`. -/
def signDiagonal (d : Fin n → ℝ) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨Matrix.diagonal fun i => signReal (d i), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, star_trivial]
    unfold signReal
    split_ifs <;> norm_num⟩

theorem signReal_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    signReal (x * y) = signReal x * signReal y := by
  unfold signReal
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · rw [ite_eq_left (mul_pos_of_neg_of_neg hx' hy'), ite_eq_right (not_lt.mpr hx'.le),
      ite_eq_right (not_lt.mpr hy'.le)]
    norm_num
  · rw [ite_eq_right (not_lt.mpr (mul_neg_of_neg_of_pos hx' hy').le),
      ite_eq_right (not_lt.mpr hx'.le), ite_eq_left hy']
    norm_num
  · rw [ite_eq_right (not_lt.mpr (mul_neg_of_pos_of_neg hx' hy').le), ite_eq_left hx',
      ite_eq_right (not_lt.mpr hy'.le)]
    norm_num
  · rw [ite_eq_left (mul_pos hx' hy'), ite_eq_left hx', ite_eq_left hy']
    norm_num

theorem signDiagonal_mul {d d' : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) (hd' : ∀ i, d' i ≠ 0) :
    signDiagonal (fun i => d i * d' i) = signDiagonal d * signDiagonal d' := by
  apply Subtype.ext
  change (Matrix.diagonal fun i => signReal (d i * d' i)) =
    Matrix.diagonal (fun i => signReal (d i)) * Matrix.diagonal fun i => signReal (d' i)
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact signReal_mul (hd i) (hd' i)

theorem upperTriangular_mul_apply_self {A C : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) (i : Fin n) :
    (A * C) i i = A i i * C i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hC hij, mul_zero]

/-! ## The extension -/

variable (s : Fin n → ℂ)

/-- The extension of a function `φ` on `O(n)`:
`x ↦ ∏_l G_l(x)^(s_l/2) G_{l+1}(x)^(-s_l/2) · φ(κ̂(x))`. -/
def extension (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ) (x : Langlands.GeneralLinear n ℝ) : ℂ :=
  gramExpression s 1 (complexify (x : Matrix (Fin n) (Fin n) ℝ)) * φ (signedOrthogonalPart x)

theorem extension_eq (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ) {x : Langlands.GeneralLinear n ℝ}
    {b κ : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin n) ℝ) (hx : (x : Matrix (Fin n) (Fin n) ℝ) = b * κ) :
    extension s φ x = (∏ l : Fin n, ((|b l l| : ℝ) : ℂ) ^ s l) *
      φ (signDiagonal (fun i => b i i) * ⟨κ, hκ⟩) := by
  have hκ' : κ * κᵀ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hκ
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  unfold extension
  congr 1
  · rw [hx, gramExpression_complexify_mul hb hd hκ' s 1, map_one, mul_one]
  · congr 1
    apply Subtype.ext
    change signedOrthogonal (x : Matrix (Fin n) (Fin n) ℝ) = _
    rw [hx, signedOrthogonal_mul hb hd hκ']
    rfl

theorem extension_unitary (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) : extension s φ (Unitary.toUnits κ) = φ κ := by
  rw [extension_eq s φ (b := 1) (κ := κ) Matrix.blockTriangular_one (fun l => by simp) κ.2
    (by rw [Matrix.one_mul]; rfl)]
  have h1 : signDiagonal (n := n) (fun i => (1 : Matrix (Fin n) (Fin n) ℝ) i i) = 1 := by
    apply Subtype.ext
    change (Matrix.diagonal fun i => signReal ((1 : Matrix (Fin n) (Fin n) ℝ) i i)) = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    simp [signReal]
  rw [h1, one_mul]
  simp

/-- **Equivariance.** -/
theorem extension_mul_left {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)
    {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφ : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) * φ κ)
    (a : Fin n → ℝˣ) (u : upperUnipotent n ℝ) (g : Langlands.GeneralLinear n ℝ) :
    extension (shiftedExponent n e) φ
        ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
          (u : Langlands.GeneralLinear n ℝ) * g) =
      principalSeriesCharacter ℝ n χ a * extension (shiftedExponent n e) φ g := by
  obtain ⟨a', u', k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  set b' : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun l => (a' l : ℝ)) *
    ((u' : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hb'def
  set B : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun l => (a l : ℝ)) *
    ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * b' with hBdef
  have hb' : b'.IsUpperTriangular := isUpperTriangular_diagonal_mul a' u'
  have hb'd : ∀ l, b' l l = a' l := diagonal_mul_apply_self a' u'
  have hB : B.IsUpperTriangular := (isUpperTriangular_diagonal_mul a u).mul
    (isUpperTriangular_diagonal_mul a' u')
  have hBd : ∀ l, B l l = a l * a' l := fun l => by
    rw [hBdef, upperTriangular_mul_apply_self (isUpperTriangular_diagonal_mul a u)
      (isUpperTriangular_diagonal_mul a' u'), diagonal_mul_apply_self, diagonal_mul_apply_self]
  have hBne : ∀ l, B l l ≠ 0 := fun l => by
    rw [hBd]
    exact mul_ne_zero (a l).ne_zero (a' l).ne_zero
  have hb'ne : ∀ l, b' l l ≠ 0 := fun l => by
    rw [hb'd]
    exact (a' l).ne_zero
  have hx : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * ((Iwasawa.diagonalUnits a' : Langlands.GeneralLinear n ℝ) *
        (u' : Langlands.GeneralLinear n ℝ) * k) : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ) = B * (k : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hBdef, hb'def]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rfl
  rw [extension_eq _ φ hB hBne hk hx, extension_eq _ φ hb' hb'ne hk (by rfl),
    principalSeriesCharacter_eq e hχ a]
  have hsign : signDiagonal (fun i => B i i) * ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ =
      signDiagonal (fun i => (a i : ℝ)) *
        (signDiagonal (fun i => b' i i) * ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩) := by
    rw [← mul_assoc]
    congr 1
    rw [← signDiagonal_mul (fun i => (a i).ne_zero) hb'ne]
    congr 1
    funext i
    rw [hBd, hb'd]
  rw [hsign, hφ]
  have hprod : (∏ l : Fin n, ((|B l l| : ℝ) : ℂ) ^ shiftedExponent n e l) =
      (∏ l : Fin n, ((|(a l : ℝ)| : ℝ) : ℂ) ^ shiftedExponent n e l) *
        ∏ l : Fin n, ((|b' l l| : ℝ) : ℂ) ^ shiftedExponent n e l := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hBd, hb'd, abs_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _)]
  rw [hprod]
  ring

/-! ## Smoothness -/

section Smooth

theorem contDiff_entry (p q : Fin n) :
    ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => y p q) := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun y => y p q, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem contDiff_det_comp {M : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ p q, ContDiff ℝ ∞ (fun y => M y p q)) : ContDiff ℝ ∞ (fun y => (M y).det) := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h (σ i) i)

theorem contDiff_paddedGram (l : ℕ) (p q : Fin n) :
    ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => paddedGram l y p q) := by
  simp only [paddedGram, Matrix.of_apply]
  split_ifs
  · simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiff.sum fun r _ => (contDiff_entry p r).mul (contDiff_entry q r)
  · exact contDiff_const

theorem contDiff_gram (l : ℕ) : ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => gram l y) :=
  contDiff_det_comp (contDiff_paddedGram l)

theorem contDiff_gramColumn (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => gramColumn i j y) := by
  refine contDiff_det_comp fun p q => ?_
  simp only [Matrix.updateCol_apply, gramColumnVector]
  split_ifs
  · exact contDiff_entry p j
  · exact contDiff_const
  · exact contDiff_paddedGram i p q

theorem contDiffAt_ofReal_cpow {f : Matrix (Fin n) (Fin n) ℝ → ℝ} {y : Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiffAt ℝ ∞ f y) (hpos : 0 < f y) (c : ℂ) :
    ContDiffAt ℝ ∞ (fun y => ((f y : ℝ) : ℂ) ^ c) y := by
  have hev : (fun y => ((f y : ℝ) : ℂ) ^ c) =ᶠ[𝓝 y]
      fun y => Complex.exp (((Real.log (f y) : ℝ) : ℂ) * c) := by
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hpos)] with z hz
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hz.ne'), ← Complex.ofReal_log hz.le]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf.log hpos.ne')).mul
    contDiffAt_const).cexp

theorem contDiffAt_mvPolynomial_eval {σ : Type*} (P : MvPolynomial σ ℂ)
    {v : σ → Matrix (Fin n) (Fin n) ℝ → ℂ} {y : Matrix (Fin n) (Fin n) ℝ}
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

/-- Gram expressions are smooth on the invertible real matrices. -/
theorem contDiffOn_gramExpression (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    ContDiffOn ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => gramExpression s P (complexify y))
      {y | IsUnit y} := by
  intro y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have hpos : ∀ l : ℕ, 0 < gram l y := fun l => by
    have := gram_pos hy.unit l
    rwa [IsUnit.unit_spec] at this
  have hG : ∀ (l : ℕ) (c : ℂ),
      ContDiffAt ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => gram l (complexify y) ^ c) y := by
    intro l c
    have : (fun y : Matrix (Fin n) (Fin n) ℝ => gram l (complexify y) ^ c) =
        fun y => ((gram l y : ℝ) : ℂ) ^ c := by
      funext z
      rw [complexify, gram_map]
      rfl
    rw [this]
    exact contDiffAt_ofReal_cpow (contDiff_gram l).contDiffAt (hpos l) c
  have hC : ∀ i j : Fin n,
      ContDiffAt ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => gramColumn i j (complexify y)) y := by
    intro i j
    have : (fun y : Matrix (Fin n) (Fin n) ℝ => gramColumn i j (complexify y)) =
        fun y => ((gramColumn i j y : ℝ) : ℂ) := by
      funext z
      rw [complexify, gramColumn_map]
      rfl
    rw [this]
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp y (contDiff_gramColumn i j).contDiffAt
  unfold gramExpression
  exact (contDiffAt_prod fun (l : Fin n) _ => (hG (l : ℕ) _).mul (hG ((l : ℕ) + 1) _)).mul
    (contDiffAt_mvPolynomial_eval P fun ij =>
      ((hC ij.1 ij.2).mul (hG (ij.1 : ℕ) _)).mul (hG ((ij.1 : ℕ) + 1) _))

end Smooth

theorem extension_eq_gramExpression {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    {P : MvPolynomial (Fin n × Fin n) ℂ}
    (hP : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ,
      φ κ = MvPolynomial.eval (fun ij => ((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ)) P)
    (x : Langlands.GeneralLinear n ℝ) :
    extension s φ x = gramExpression s P (complexify (x : Matrix (Fin n) (Fin n) ℝ)) := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
  set b : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun l => (a l : ℝ)) *
    ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hbdef
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul a u
  have hd : ∀ l, b l l ≠ 0 := fun l => by
    rw [hbdef, diagonal_mul_apply_self]
    exact (a l).ne_zero
  have hx : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * k : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) = b * (k : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [extension_eq s φ hb hd hk hx, hx,
    gramExpression_complexify_mul hb hd (mul_transpose_eq_one_of_mem hk), hP]
  congr 1
  refine congrArg (fun v => MvPolynomial.eval v P) (funext fun ij => ?_)
  change ((((Matrix.diagonal fun i => signReal (b i i)) * (k : Matrix (Fin n) (Fin n) ℝ))
    ij.1 ij.2 : ℝ) : ℂ) = _
  rw [Matrix.diagonal_mul]

theorem contMDiff_extension {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    {P : MvPolynomial (Fin n × Fin n) ℂ}
    (hP : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ,
      φ κ = MvPolynomial.eval (fun ij => ((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ)) P) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (extension s φ) :=
  contMDiff_of_contDiffOn (contDiffOn_gramExpression s P)
    fun g => extension_eq_gramExpression s hP g

/-! ## The extension lies in the principal series and is `O(n)`-finite -/

/-- The extension as a linear map. -/
def extensionLinear : (Matrix.unitaryGroup (Fin n) ℝ → ℂ) →ₗ[ℂ]
    (Langlands.GeneralLinear n ℝ → ℂ) where
  toFun := extension s
  map_add' φ ψ := funext fun x => by
    simp only [extension, Pi.add_apply, mul_add]
  map_smul' c φ := funext fun x => by
    simp only [extension, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

variable {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
  (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)

include hχ in
theorem extension_mem_principalSeries {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφc : Continuous φ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))))
    (hφM : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) * φ κ) :
    extension (shiftedExponent n e) φ ∈ principalSeries ℝ n χ := by
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_finiteDimensional_span
    hφc hfin
  exact ⟨contMDiff_extension _ hP, extension_mul_left e hχ hφM⟩

theorem finiteDimensional_translate {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))))
    (k₀ : Matrix.unitaryGroup (Fin n) ℝ) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k * k₀))) := by
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => φ (x * k * k₀)) ≤ Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
        fun x => φ (x * k)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k * k₀, funext fun x => by
      show φ (x * (k * k₀)) = φ (x * k * k₀)
      rw [mul_assoc]⟩
  exact Submodule.finiteDimensional_of_le hle

include hχ in
theorem rightTranslation_extension {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφc : Continuous φ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))))
    (hφM : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) * φ κ)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (Unitary.toUnits k)
        (extension (shiftedExponent n e) φ) =
      extension (shiftedExponent n e) (fun κ => φ (κ * k)) := by
  have h₁ := rightTranslation_mem_principalSeries (χ := χ)
    (extension_mem_principalSeries e hχ hφc hfin hφM) (Unitary.toUnits k)
  have h₂ : extension (shiftedExponent n e) (fun κ => φ (κ * k)) ∈ principalSeries ℝ n χ :=
    extension_mem_principalSeries e hχ (hφc.comp (continuous_id.mul continuous_const))
      (finiteDimensional_translate hfin k) fun a κ => by
        show φ (signDiagonal _ * κ * k) = _ * φ (κ * k)
        rw [mul_assoc, hφM]
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries h₁ h₂ fun g hg => ?_
  have hgu : g = Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  rw [hgu]
  change extension _ φ (Unitary.toUnits _ * Unitary.toUnits k) = _
  rw [← map_mul, extension_unitary, extension_unitary]

include hχ in
/-- **Extension.** -/
theorem extension_mem_kFiniteFunctions {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφc : Continuous φ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))))
    (hφM : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) * φ κ) :
    extension (shiftedExponent n e) φ ∈
      kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
  refine Submodule.mem_inf.mpr ⟨extension_mem_principalSeries e hχ hφc hfin hφM, ?_⟩
  rw [mem_kFiniteVectors_iff]
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
        (extension (shiftedExponent n e) φ)) ≤
      (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
        fun x => φ (x * k))).map (extensionLinear (shiftedExponent n e)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have hk : (k : Langlands.GeneralLinear n ℝ) = Unitary.toUnits
        (⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ :
          Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
    simp only
    rw [hk, rightTranslation_extension e hχ hφc hfin hφM]
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end PrincipalSeriesExtension

open PrincipalSeriesExtension GramFormula

/-- **Statement (extension of `O(n)`-finite functions to principal series).** Let `ds` be a list
of real blocks and `φ : O(n) → ℂ` a continuous function whose right translates span a
finite-dimensional space and which satisfies
`φ(diag(sgn a) κ) = principalSeriesCharacter ℝ n (realPositionCharacter ds) (sgn a) · φ(κ)` for all
`a ∈ (ℝˣ)ⁿ` and `κ ∈ O(n)`. Then `φ` is the restriction to `O(n)` of an `O(n)`-finite function of
the smooth principal series of the position characters of `ds`. -/
def PrincipalSeriesExtensionStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ), Continuous φ →
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))) →
    (∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) * φ κ) →
    ∃ f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n),
      ∀ κ : Matrix.unitaryGroup (Fin n) ℝ, f (Unitary.toUnits κ) = φ κ

theorem principalSeriesExtension : PrincipalSeriesExtensionStatement :=
  fun _ ds _ hφc hfin hφM =>
    ⟨_, extension_mem_kFiniteFunctions (realPositionExponent ds)
      (realPositionCharacter_eq_signUnit_mul ds) hφc hfin hφM, extension_unitary _ _⟩

end Langlands.Archimedean
