import Langlands.Representation.Archimedean.ComplexGLTwoIrreducibleCore
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.UnitaryFinitePolynomial

/-!
# `U(2)`-finite functions of `GL_2(ℂ)` principal series as bottom-row polynomials

For complex characters `d`, `e`, every `U(2)`-finite function `f` of the standard module of
`[d, e]` is `realize Φ s P` with `Φ = unitChar l_d (t_d + 1/2)` and, for some level `J`,
`s = s_J` and `P` bihomogeneous of bidegree `(a_J, b_J)` (`exists_isRealized`).
-/

noncomputable section

open MvPolynomial
open scoped Manifold ContDiff Matrix Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.GLTwoKFinite

open GLTwoPoly GLTwoModel LocalFactor.Archimedean Langlands.GeneralLinear

/-! ## Characters of `ℂˣ` -/

theorem unitChar_mul (μ : ℤ) (w : ℂ) {z z' : ℂ} (hz : z ≠ 0) (hz' : z' ≠ 0) :
    unitChar μ w (z * z') = unitChar μ w z * unitChar μ w z' := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hn' : ‖z'‖ ≠ 0 := norm_ne_zero_iff.mpr hz'
  simp only [unitChar, norm_mul, Complex.ofReal_mul, Real.log_mul hn hn']
  rw [show z * z' / ((‖z‖ : ℂ) * (‖z'‖ : ℂ)) = (z / ‖z‖) * (z' / ‖z'‖) by
    field_simp, mul_zpow, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem unitChar_ofReal (μ : ℤ) (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    unitChar μ w (ρ : ℂ) = Complex.exp (2 * w * (Real.log ρ : ℂ)) := by
  have h1 : (ρ : ℂ) / ((‖(ρ : ℂ)‖ : ℝ) : ℂ) = 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hρ.le, div_self (by exact_mod_cast hρ.ne')]
  rw [unitChar, h1, one_zpow, one_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]

theorem unitChar_of_norm_eq_one (μ : ℤ) (w : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    unitChar μ w ζ = ζ ^ μ := by
  rw [unitChar, hζ, Real.log_one]
  simp

theorem unitChar_ne_zero (μ : ℤ) (w : ℂ) {z : ℂ} (hz : z ≠ 0) : unitChar μ w z ≠ 0 := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  exact mul_ne_zero (zpow_ne_zero _ (div_ne_zero hz hn)) (Complex.exp_ne_zero _)

theorem differentiableAt_unitChar (μ : ℤ) (w : ℂ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (unitChar μ w) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h1 : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z := differentiableAt_id.norm ℝ hz
  have h2 : DifferentiableAt ℝ (fun u : ℂ => u / (‖u‖ : ℂ)) z := by
    have : (fun u : ℂ => u / (‖u‖ : ℂ)) = fun u : ℂ => u * (Complex.ofRealCLM (‖u‖⁻¹)) := by
      funext u; simp [div_eq_mul_inv]
    rw [this]
    exact differentiableAt_id.mul (Complex.ofRealCLM.differentiableAt.comp z (h1.inv hn))
  have hq : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz (Complex.ofReal_ne_zero.mpr hn)
  have hz' : DifferentiableAt ℂ (fun v : ℂ => v ^ μ) (z / (‖z‖ : ℂ)) :=
    differentiableAt_zpow.mpr (Or.inl hq)
  have h3 : DifferentiableAt ℝ (fun u : ℂ => (u / (‖u‖ : ℂ)) ^ μ) z := by
    have hF : HasFDerivAt (fun v : ℂ => v ^ μ)
        ((fderiv ℂ (fun v : ℂ => v ^ μ) (z / (‖z‖ : ℂ))).restrictScalars ℝ) (z / (‖z‖ : ℂ)) :=
      hz'.hasFDerivAt.restrictScalars ℝ
    exact (hF.comp z h2.hasFDerivAt).differentiableAt
  have h4 : DifferentiableAt ℝ (fun u : ℂ => Complex.exp (2 * w * (Real.log ‖u‖ : ℂ))) z :=
    ((Complex.ofRealCLM.differentiableAt.comp z
      ((Real.differentiableAt_log hn).comp z h1)).const_mul (2 * w)).cexp
  exact h3.mul h4

/-! ## The principal series character of `GL_2(ℂ)` -/

variable (d e : ComplexCharacterData)

/-- The determinant factor `Φ(δ) = (δ/|δ|)^{l_d} |δ|^{2 t_d + 1}`. -/
def Phi : ℂ → ℂ := unitChar d.weight (d.exponent + 1 / 2)

theorem psc_two (a : Fin 2 → ℂˣ) :
    principalSeriesCharacter ℂ 2 (complexPositionCharacter [d, e]) a =
      unitChar d.weight (d.exponent + 1 / 2) (a 0) *
        unitChar e.weight (e.exponent - 1 / 2) (a 1) := by
  rw [principalSeriesCharacter_eq, Fin.prod_univ_two]
  simp only [posWeight, posExponent, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  congr 2 <;> ring

variable {d e}

/-- `f(diag(a) h) = χ(a) f(h)` on the standard module of `[d, e]`. -/
theorem diag_mul_apply {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 2 [d, e]) (a : Fin 2 → ℂˣ)
    (h : Langlands.GeneralLinear 2 ℂ) :
    f ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear 2 ℂ) * h) =
      unitChar d.weight (d.exponent + 1 / 2) (a 0) *
        unitChar e.weight (e.exponent - 1 / 2) (a 1) * f h := by
  have := hf.2 a 1 h
  rw [OneMemClass.coe_one, mul_one] at this
  rw [this, psc_two]

/-- Two elements with the same bottom row and determinant differ by an upper unipotent
element on the left. -/
theorem mul_inv_mem_upperUnipotent {g h : Langlands.GeneralLinear 2 ℂ}
    (hrow : row (g : Matrix (Fin 2) (Fin 2) ℂ) = row (h : Matrix (Fin 2) (Fin 2) ℂ))
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = (h : Matrix (Fin 2) (Fin 2) ℂ).det) :
    g * h⁻¹ ∈ GeneralLinear.upperUnipotent 2 ℂ := by
  have hd : (h : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := det_ne_zero h
  have hinv : ((h⁻¹ : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (h : Matrix (Fin 2) (Fin 2) ℂ).det⁻¹ • (h : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  have hr0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 :=
    congrFun hrow 0
  have hr1 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 :=
    congrFun hrow 1
  have hdet' := hdet
  rw [Matrix.det_fin_two, hr0, hr1] at hdet'
  have hentry : ∀ i j : Fin 2, ((g * h⁻¹ : Langlands.GeneralLinear 2 ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) i j = (h : Matrix (Fin 2) (Fin 2) ℂ).det⁻¹ *
        ∑ k, (g : Matrix (Fin 2) (Fin 2) ℂ) i k * (h : Matrix (Fin 2) (Fin 2) ℂ).adjugate k j := by
    intro i j
    rw [Units.val_mul, hinv, Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    change ((g * h⁻¹ : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
    rw [hentry, Fin.sum_univ_two, Matrix.adjugate_fin_two, hr0, hr1]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
    ring
  · intro i
    change ((g * h⁻¹ : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i i = 1
    rw [hentry, Fin.sum_univ_two, Matrix.adjugate_fin_two]
    have hD := Matrix.det_fin_two (h : Matrix (Fin 2) (Fin 2) ℂ)
    fin_cases i
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [show (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * -(h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
          (h : Matrix (Fin 2) (Fin 2) ℂ).det by linear_combination hdet']
      exact inv_mul_cancel₀ hd
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
      rw [hr0, hr1, show (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * -(h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 +
          (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
          (h : Matrix (Fin 2) (Fin 2) ℂ).det by linear_combination -hD]
      exact inv_mul_cancel₀ hd

/-- Functions of the standard module depend only on the bottom row and the determinant. -/
theorem eq_of_row_det {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 2 [d, e]) {g h : Langlands.GeneralLinear 2 ℂ}
    (hrow : row (g : Matrix (Fin 2) (Fin 2) ℂ) = row (h : Matrix (Fin 2) (Fin 2) ℂ))
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = (h : Matrix (Fin 2) (Fin 2) ℂ).det) :
    f g = f h := by
  have hu := mul_inv_mem_upperUnipotent hrow hdet
  have := hf.2 1 ⟨g * h⁻¹, hu⟩ h
  rw [map_one, one_mul, Subgroup.coe_mk, inv_mul_cancel_right, psc_two] at this
  simpa [unitChar_of_norm_eq_one] using this

/-! ## The section `u ↦ !![ū₁, -ū₀; u₀, u₁]` over the unit sphere -/

theorem bottomMat_mem_unitaryGroup {u : Fin 2 → ℂ} (hu : nrm u = 1) :
    bottomMat u ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : u 0 * starRingEnd ℂ (u 0) + u 1 * starRingEnd ℂ (u 1) = 1 := by
    have := ev_N u
    rw [hu, Complex.ofReal_one] at this
    simpa [N, ev_add, ev_mul, ev_z, ev_w] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bottomMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
    first | linear_combination h | ring

/-- `bottomMat u` as an element of `U(2)` when `|u| = 1`. -/
def kU (u : Fin 2 → ℂ) (hu : nrm u = 1) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨bottomMat u, bottomMat_mem_unitaryGroup hu⟩

/-- The entries of `bottomMat u` and their conjugates as polynomials in `u, ū`. -/
def subst : (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) → Pol
  | Sum.inl ij => (!![w 1, -w 0; z 0, z 1] : Matrix (Fin 2) (Fin 2) Pol) ij.1 ij.2
  | Sum.inr ij => (!![z 1, -z 0; w 0, w 1] : Matrix (Fin 2) (Fin 2) Pol) ij.1 ij.2

theorem coordValue_kU (u : Fin 2 → ℂ) (hu : nrm u = 1) :
    UnitaryFinitePolynomial.coordValue (kU u hu) = fun c => ev u (subst c) := by
  funext c
  rcases c with ⟨i, j⟩ | ⟨i, j⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [UnitaryFinitePolynomial.coordValue, kU, bottomMat, subst, ev, z, w]

theorem eval_coordValue_kU (u : Fin 2 → ℂ) (hu : nrm u = 1)
    (Q : MvPolynomial ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ℂ) :
    MvPolynomial.eval (UnitaryFinitePolynomial.coordValue (kU u hu)) Q = ev u (bind₁ subst Q) := by
  rw [coordValue_kU]
  change _ = aeval _ (bind₁ subst Q)
  rw [aeval_bind₁]
  rfl

/-! ## The bottom-row decomposition -/

theorem row_diag_mul (a : Fin 2 → ℂˣ) (B : Langlands.GeneralLinear 2 ℂ) :
    row (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear 2 ℂ) * B :
      Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (a 1 : ℂ) • row (B : Matrix (Fin 2) (Fin 2) ℂ) := by
  funext k
  simp [row, Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]

theorem det_diag_mul (a : Fin 2 → ℂˣ) (B : Langlands.GeneralLinear 2 ℂ) :
    (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear 2 ℂ) * B :
      Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
      (a 0 : ℂ) * (a 1 : ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ).det := by
  rw [Units.val_mul, Matrix.det_mul, Iwasawa.diagonalUnits_val, Matrix.det_diagonal,
    Fin.prod_univ_two]

theorem nrm_smul (c : ℂ) (r : Fin 2 → ℂ) : nrm (c • r) = ‖c‖ ^ 2 * nrm r := by
  simp only [nrm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem coe_toUnits_kU (u : Fin 2 → ℂ) (hu : nrm u = 1) :
    ((Unitary.toUnits (kU u hu) : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      bottomMat u := rfl

variable (d e) in
/-- The exponent `t_e - t_d - 1 = (A + B)/2` of `|r|²` in the bottom-row decomposition. -/
def e0 : ℂ := e.exponent - d.exponent - 1

/-- **Bottom-row decomposition.** If `f` is given on `U(2)` by the polynomial `Q`, then
`f(g) = Φ(det g) · (|r|²)^{t_e - t_d - 1} · Q'(u, ū)` with `r` the bottom row of `g`,
`u = r/|r|` and `Q' = bind₁ subst Q`. -/
theorem eq_mul_ev {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 2 [d, e])
    (Q : MvPolynomial ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ℂ)
    (hQ : ∀ k : Matrix.unitaryGroup (Fin 2) ℂ,
      f (Unitary.toUnits k) = MvPolynomial.eval (UnitaryFinitePolynomial.coordValue k) Q)
    (g : Langlands.GeneralLinear 2 ℂ) :
    f g = Phi d (g : Matrix (Fin 2) (Fin 2) ℂ).det *
      (nrm (row (g : Matrix (Fin 2) (Fin 2) ℂ)) : ℂ) ^ e0 d e *
        ev ((((Real.sqrt (nrm (row (g : Matrix (Fin 2) (Fin 2) ℂ))))⁻¹ : ℝ) : ℂ) •
          row (g : Matrix (Fin 2) (Fin 2) ℂ)) (bind₁ subst Q) := by
  set r := row (g : Matrix (Fin 2) (Fin 2) ℂ) with hr
  set δ := (g : Matrix (Fin 2) (Fin 2) ℂ).det with hδ
  have hN : 0 < nrm r := nrm_pos_of_det_ne_zero (det_ne_zero g)
  set ρ := Real.sqrt (nrm r) with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hN
  have hρ2 : ρ ^ 2 = nrm r := Real.sq_sqrt hN.le
  have hδ0 : δ ≠ 0 := det_ne_zero g
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set u : Fin 2 → ℂ := ((ρ⁻¹ : ℝ) : ℂ) • r with hu_def
  have hu : nrm u = 1 := by
    rw [hu_def, nrm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),
      inv_pow, hρ2, inv_mul_cancel₀ hN.ne']
  set a : Fin 2 → ℂˣ := ![Units.mk0 (δ / ρ) (div_ne_zero hδ0 hρc), Units.mk0 (ρ : ℂ) hρc]
    with ha
  have hrow : row (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear 2 ℂ) *
      Unitary.toUnits (kU u hu) : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      r := by
    rw [row_diag_mul, coe_toUnits_kU, row_bottomMat, hu_def, smul_smul]
    simp only [ha, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Units.val_mk0]
    rw [Complex.ofReal_inv, mul_inv_cancel₀ hρc, one_smul]
  have hdet : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear 2 ℂ) *
      Unitary.toUnits (kU u hu) : Langlands.GeneralLinear 2 ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).det = δ := by
    rw [det_diag_mul, coe_toUnits_kU, det_bottomMat, hu]
    simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.val_mk0,
      Complex.ofReal_one, mul_one]
    field_simp
  rw [eq_of_row_det hf hrow.symm hdet.symm, diag_mul_apply hf, hQ, eval_coordValue_kU]
  simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.val_mk0]
  have h1 : δ / (ρ : ℂ) = δ * ((ρ⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv, div_eq_mul_inv]
  have hρi : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ
  rw [h1, unitChar_mul _ _ hδ0 (by exact_mod_cast hρi.ne'), unitChar_ofReal _ _ hρi,
    unitChar_ofReal _ _ hρ, Phi, e0,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hN.ne' : (nrm r : ℂ) ≠ 0),
    ← Complex.ofReal_log hN.le, ← hρ2, Real.log_pow, Real.log_inv]
  have : Complex.exp (2 * (d.exponent + 1 / 2) * ((-Real.log ρ : ℝ) : ℂ)) *
      Complex.exp (2 * (e.exponent - 1 / 2) * (Real.log ρ : ℂ)) =
      Complex.exp ((((2 : ℕ) : ℝ) * Real.log ρ : ℝ) * (e.exponent - d.exponent - 1)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc _ = unitChar d.weight (d.exponent + 1 / 2) δ *
        (Complex.exp (2 * (d.exponent + 1 / 2) * ((-Real.log ρ : ℝ) : ℂ)) *
          Complex.exp (2 * (e.exponent - 1 / 2) * (Real.log ρ : ℂ))) *
        ev u (bind₁ subst Q) := by ring
    _ = _ := by rw [this]

/-- **The phase relation.** On the unit sphere, `Q'(ζ u, conj(ζ u)) = ζ^{l_e - l_d} Q'(u, ū)`
for `|ζ| = 1`. -/
theorem ev_smul_phase {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 2 [d, e])
    (Q : MvPolynomial ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ℂ)
    (hQ : ∀ k : Matrix.unitaryGroup (Fin 2) ℂ,
      f (Unitary.toUnits k) = MvPolynomial.eval (UnitaryFinitePolynomial.coordValue k) Q)
    {u : Fin 2 → ℂ} (hu : nrm u = 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ev (ζ • u) (bind₁ subst Q) = ζ ^ (e.weight - d.weight) * ev u (bind₁ subst Q) := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hu' : nrm (ζ • u) = 1 := by rw [nrm_smul, hζ, one_pow, one_mul, hu]
  set a : Fin 2 → ℂˣ := ![Units.mk0 ζ⁻¹ (inv_ne_zero hζ0), Units.mk0 ζ hζ0] with ha
  have hrow : row (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear 2 ℂ) *
      Unitary.toUnits (kU u hu) : Langlands.GeneralLinear 2 ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      row ((Unitary.toUnits (kU (ζ • u) hu') : Langlands.GeneralLinear 2 ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [row_diag_mul, coe_toUnits_kU, coe_toUnits_kU, row_bottomMat, row_bottomMat]
    simp [ha]
  have hdet : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear 2 ℂ) *
      Unitary.toUnits (kU u hu) : Langlands.GeneralLinear 2 ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).det =
      ((Unitary.toUnits (kU (ζ • u) hu') : Langlands.GeneralLinear 2 ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [det_diag_mul, coe_toUnits_kU, coe_toUnits_kU, det_bottomMat, det_bottomMat, hu, hu']
    simp [ha, hζ0]
  have h := eq_of_row_det hf hrow hdet
  rw [diag_mul_apply hf, hQ, hQ, eval_coordValue_kU, eval_coordValue_kU] at h
  simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Units.val_mk0] at h
  have hζi : ‖ζ⁻¹‖ = 1 := by rw [norm_inv, hζ, inv_one]
  rw [unitChar_of_norm_eq_one _ _ hζi, unitChar_of_norm_eq_one _ _ hζ] at h
  rw [← h, zpow_sub₀ hζ0, inv_zpow', zpow_neg]
  ring

/-! ## Separating phases -/

/-- The Cayley map `t ↦ (1 + i t)/(1 - i t)` from `ℝ` to the unit circle. -/
def cayley (t : ℝ) : ℂ := (1 + t * Complex.I) / (1 - t * Complex.I)

theorem one_sub_ne_zero (t : ℝ) : (1 : ℂ) - t * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem norm_cayley (t : ℝ) : ‖cayley t‖ = 1 := by
  have h : (1 : ℂ) + t * Complex.I = starRingEnd ℂ (1 - t * Complex.I) := by
    simp [map_sub, Complex.conj_ofReal]
  rw [cayley, norm_div, h, Complex.norm_conj, div_self]
  exact norm_ne_zero_iff.mpr (one_sub_ne_zero t)

theorem cayley_injective : Function.Injective cayley := by
  intro t s h
  rw [cayley, cayley, div_eq_div_iff (one_sub_ne_zero t) (one_sub_ne_zero s)] at h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem infinite_circle : {ζ : ℂ | ‖ζ‖ = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem cayley_injective fun t => ?_
  exact norm_cayley t

/-- **Phase separation.** If `Σ_i ζ^{p_i} ζ^{-q_i} v_i = ζ^{m} Σ_i v_i` for all `|ζ| = 1`, then
the terms with `p_i - q_i = m` already sum to `Σ_i v_i`. -/
theorem sum_filter_eq_of_phase {ι : Type*} (s : Finset ι) (p q : ι → ℕ) (v : ι → ℂ) (m : ℤ)
    (h : ∀ ζ : ℂ, ‖ζ‖ = 1 →
      ∑ i ∈ s, ζ ^ p i * ζ⁻¹ ^ q i * v i = ζ ^ m * ∑ i ∈ s, v i) :
    ∑ i ∈ s with (p i : ℤ) - q i = m, v i = ∑ i ∈ s, v i := by
  classical
  set K : ℕ := s.sup q + m.natAbs with hK
  have hqK : ∀ i ∈ s, q i ≤ K := fun i hi => le_add_right (Finset.le_sup hi)
  have hmK : 0 ≤ m + K := by
    rw [hK]
    push_cast
    have := neg_abs_le m
    omega
  set F : Polynomial ℂ := ∑ i ∈ s, Polynomial.C (v i) * Polynomial.X ^ (p i + K - q i) -
    Polynomial.C (∑ i ∈ s, v i) * Polynomial.X ^ (m + K).toNat with hF
  have hroot : ∀ ζ : ℂ, ‖ζ‖ = 1 → F.eval ζ = 0 := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
    have e1 : ∀ i ∈ s, ζ ^ (p i + K - q i) = ζ ^ K * (ζ ^ p i * ζ⁻¹ ^ q i) := by
      intro i hi
      have hq := hqK i hi
      rw [show p i + K - q i = p i + (K - q i) by omega, pow_add, inv_pow,
        show K = (K - q i) + q i by omega, pow_add]
      field_simp
      rw [show K - q i + q i - q i = K - q i by omega]
    have e2 : ζ ^ (m + K).toNat = ζ ^ K * ζ ^ m := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hmK, zpow_add₀ hζ0, zpow_natCast, mul_comm]
    simp only [hF, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, e2]
    rw [Finset.sum_congr rfl fun i hi => by rw [e1 i hi]]
    have e3 : ∑ i ∈ s, v i * (ζ ^ K * (ζ ^ p i * ζ⁻¹ ^ q i)) =
        ζ ^ K * ∑ i ∈ s, ζ ^ p i * ζ⁻¹ ^ q i * v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e3, h ζ hζ]
    ring
  have hF0 : F = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact infinite_circle.mono fun ζ hζ => hroot ζ hζ
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff (m + K).toNat) hF0
  simp only [hF, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero, ↓reduceIte, mul_one] at hc
  rw [sub_eq_zero] at hc
  rw [Finset.sum_filter, ← hc]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hq := hqK i hi
  by_cases hpq : (p i : ℤ) - q i = m
  · rw [if_pos hpq, if_pos (by omega), mul_one]
  · rw [if_neg hpq, if_neg (by omega), mul_zero]

/-! ## Monomials -/

theorem monomial_mem_Eig (d : Var →₀ ℕ) (a : ℂ) :
    monomial d a ∈ Eig (degZ d : ℂ) (degW d : ℂ) := by
  classical
  rw [mem_Eig_iff_coeff]
  intro d' hd'
  rw [coeff_monomial] at hd'
  split_ifs at hd' with h
  · subst h; exact ⟨rfl, rfl⟩
  · exact absurd rfl hd'

theorem N_pow_mul_mem {α β : ℂ} {P : Pol} (hP : P ∈ Eig α β) (k : ℕ) :
    N ^ k * P ∈ Eig (α + k) (β + k) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    have := N_mul_mem ih
    rw [pow_succ', mul_assoc]
    push_cast
    rwa [← add_assoc, ← add_assoc]

theorem ev_smul_monomial (c : ℂ) (u : Fin 2 → ℂ) (d : Var →₀ ℕ) (a : ℂ) :
    ev (c • u) (monomial d a) =
      c ^ degZ d * starRingEnd ℂ c ^ degW d * ev u (monomial d a) := by
  simp only [ev, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
    smul_eq_mul, map_mul, mul_pow, degZ, degW, pow_add]
  ring

theorem conj_eq_inv {ζ : ℂ} (hζ : ‖ζ‖ = 1) : starRingEnd ℂ ζ = ζ⁻¹ := by
  have h : starRingEnd ℂ ζ * ζ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    simp
  exact eq_inv_of_mul_eq_one_left h

theorem inv_sqrt_pow {N' : ℝ} (hN : 0 < N') (n : ℕ) :
    (((Real.sqrt N')⁻¹ : ℝ) : ℂ) ^ n = (N' : ℂ) ^ (-(n : ℂ) / 2) := by
  have hρ : 0 < Real.sqrt N' := Real.sqrt_pos.mpr hN
  have h2 : ((Real.sqrt N') ^ 2 : ℝ) = N' := Real.sq_sqrt hN.le
  have hlog : Real.log N' = 2 * Real.log (Real.sqrt N') := by
    conv_lhs => rw [← h2]
    rw [Real.log_pow]; push_cast; ring
  have hρ' : 0 < (Real.sqrt N')⁻¹ := inv_pos.mpr hρ
  rw [show (((Real.sqrt N')⁻¹ : ℝ) : ℂ) ^ n = (((Real.sqrt N')⁻¹ ^ n : ℝ) : ℂ) by push_cast; ring,
    ← Real.exp_log (pow_pos hρ' n), Complex.ofReal_exp, Real.log_pow, Real.log_inv,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    ← Complex.ofReal_log hN.le, hlog]
  congr 1
  push_cast
  ring

theorem nrm_unit {r : Fin 2 → ℂ} (hr : 0 < nrm r) :
    nrm ((((Real.sqrt (nrm r))⁻¹ : ℝ) : ℂ) • r) = 1 := by
  have hρ : 0 < Real.sqrt (nrm r) := Real.sqrt_pos.mpr hr
  rw [nrm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le), inv_pow,
    Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne']

theorem term_eq {N' : ℝ} (hN : 0 < N') (e0' : ℂ) (m : ℤ) (J : ℕ) (dd : Var →₀ ℕ)
    (hc : (degZ dd : ℤ) - degW dd = m) (hj : degZ dd - m.toNat ≤ J) (E : ℂ) :
    (N' : ℂ) ^ e0' * ((((Real.sqrt N')⁻¹ : ℝ) : ℂ) ^ (degZ dd + degW dd) * E) =
      (N' : ℂ) ^ (e0' + (m : ℂ) / 2 - ((m.toNat + J : ℕ) : ℂ)) *
        ((N' : ℂ) ^ (J - (degZ dd - m.toNat)) * E) := by
  have hNc : (N' : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [inv_sqrt_pow hN, ← Complex.cpow_natCast (N' : ℂ) (J - _), ← mul_assoc, ← mul_assoc,
    ← Complex.cpow_add _ _ hNc, ← Complex.cpow_add _ _ hNc]
  have hz : m.toNat ≤ degZ dd := by omega
  have e2 : ((J - (degZ dd - m.toNat) : ℕ) : ℂ) = (J : ℂ) - (degZ dd : ℂ) + (m.toNat : ℂ) := by
    rw [Nat.cast_sub hj, Nat.cast_sub hz]; ring
  have e3 : (degW dd : ℂ) = (degZ dd : ℂ) - (m : ℂ) := by
    have : ((degW dd : ℤ) : ℂ) = ((degZ dd : ℤ) : ℂ) - (m : ℂ) := by
      rw [← hc]; push_cast; ring
    exact_mod_cast this
  congr 2
  rw [e2]
  push_cast
  rw [e3]
  ring

open GLTwoCore in
/-- **`U(2)`-finite functions are bottom-row polynomials.** Every `U(2)`-finite function of
the standard module of `[d, e]` is `realize Φ s_J P` for some level `J` and some
`P ∈ Eig a_J b_J`, with `m = l_e - l_d`, `A = (t_e - t_d - 1) + m/2`. -/
theorem exists_isRealized (x : KF2 [d, e]) :
    ∃ (J : ℕ) (P : Pol), P ∈ Eig (la (e.weight - d.weight) J) (lb (e.weight - d.weight) J) ∧
      IsRealized (Phi d) (ls (e0 d e + ((e.weight - d.weight : ℤ) : ℂ) / 2)
        (e.weight - d.weight) J) P x := by
  classical
  set m : ℤ := e.weight - d.weight with hm
  have hf : (x : Langlands.GeneralLinear 2 ℂ → ℂ) ∈ complexStandardModule 2 [d, e] := x.2.1
  have hcont : Continuous (x : Langlands.GeneralLinear 2 ℂ → ℂ) :=
    (smooth_of_mem x).continuous
  obtain ⟨Q, hQ1⟩ :=
    UnitaryFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors hcont x.2.2 1
  have hQ : ∀ k : Matrix.unitaryGroup (Fin 2) ℂ,
      (x : Langlands.GeneralLinear 2 ℂ → ℂ) (Unitary.toUnits k) =
        MvPolynomial.eval (UnitaryFinitePolynomial.coordValue k) Q := fun k => by
    rw [← hQ1 k, one_mul]
  set Q' : Pol := bind₁ subst Q with hQ'
  set Sg := Q'.support.filter (fun dd => (degZ dd : ℤ) - degW dd = m) with hSg
  set jd : (Var →₀ ℕ) → ℕ := fun dd => degZ dd - m.toNat with hjd
  set J := Sg.sup jd with hJ
  refine ⟨J, ∑ dd ∈ Sg, N ^ (J - jd dd) * monomial dd (Q'.coeff dd), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun dd hdd => ?_
    have hc := (Finset.mem_filter.mp hdd).2
    have hj : jd dd ≤ J := Finset.le_sup hdd
    have h := N_pow_mul_mem (monomial_mem_Eig dd (Q'.coeff dd)) (J - jd dd)
    have hjd' : jd dd = degZ dd - m.toNat := rfl
    have h1 : (m.toNat : ℤ) = max m 0 := Int.toNat_eq_max m
    have h2 : ((-m).toNat : ℤ) = max (-m) 0 := Int.toNat_eq_max (-m)
    have e1 : la m J = degZ dd + (J - jd dd) := by simp only [la]; omega
    have e2 : lb m J = degW dd + (J - jd dd) := by simp only [lb]; omega
    rw [e1, e2]
    push_cast
    exact h
  · intro g
    rw [eq_mul_ev hf Q hQ g]
    set r := row (g : Matrix (Fin 2) (Fin 2) ℂ) with hr
    have hN : 0 < nrm r := nrm_pos_of_det_ne_zero (det_ne_zero g)
    set u : Fin 2 → ℂ := (((Real.sqrt (nrm r))⁻¹ : ℝ) : ℂ) • r with hu_def
    have hu : nrm u = 1 := nrm_unit hN
    have hexp : ∀ (c : ℂ) (v : Fin 2 → ℂ), ev (c • v) Q' =
        ∑ dd ∈ Q'.support, c ^ degZ dd * starRingEnd ℂ c ^ degW dd *
          ev v (monomial dd (Q'.coeff dd)) := by
      intro c v
      conv_lhs => rw [Q'.as_sum]
      simp only [ev, map_sum] at *
      exact Finset.sum_congr rfl fun dd _ => ev_smul_monomial c v dd _
    have hsum : ev u Q' = ∑ dd ∈ Q'.support, ev u (monomial dd (Q'.coeff dd)) := by
      have := hexp 1 u
      simpa using this
    have hphase := sum_filter_eq_of_phase Q'.support degZ degW
      (fun dd => ev u (monomial dd (Q'.coeff dd))) m (by
        intro ζ hζ
        rw [← hsum, ← ev_smul_phase hf Q hQ hu hζ, hexp, conj_eq_inv hζ])
    rw [hsum, ← hphase, realize, ← hSg, ← hr]
    simp only [ev, map_sum, map_mul, map_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun dd hdd => ?_
    have hc := (Finset.mem_filter.mp hdd).2
    have hj : jd dd ≤ J := Finset.le_sup hdd
    have hsm : eval (Sum.elim u fun k => starRingEnd ℂ (u k)) (monomial dd (Q'.coeff dd)) =
        (((Real.sqrt (nrm r))⁻¹ : ℝ) : ℂ) ^ degZ dd * (((Real.sqrt (nrm r))⁻¹ : ℝ) : ℂ) ^ degW dd *
          eval (Sum.elim r fun k => starRingEnd ℂ (r k)) (monomial dd (Q'.coeff dd)) := by
      have := ev_smul_monomial (((Real.sqrt (nrm r))⁻¹ : ℝ) : ℂ) r dd (Q'.coeff dd)
      simp only [ev, Complex.conj_ofReal] at this
      exact this
    have hNev : eval (Sum.elim r fun k => starRingEnd ℂ (r k)) N = (nrm r : ℂ) := ev_N r
    rw [hsm, ← pow_add, hNev, mul_assoc,
      term_eq hN (e0 d e) m J dd hc hj
        (eval (Sum.elim r fun k => starRingEnd ℂ (r k)) (monomial dd (Q'.coeff dd)))]
    simp only [ls, la, hjd]
    ring

end Langlands.Archimedean.GLTwoKFinite
