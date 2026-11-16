import Langlands.Representation.Archimedean.ComplexJacquetDual

/-!
# The twist `g ↦ w₀ (gᵀ)⁻¹` of `GL_n(ℂ)` and principal series

`twist g = w₀ (gᵀ)⁻¹`, with `w₀` the antidiagonal permutation matrix, is an involution of
`GL_n(ℂ)` preserving `U(n)`. Pulling back along it carries the principal series of characters
`χ_l` to that of `z ↦ χ_{n-1-l}(z⁻¹)`, and `U(n)`-finite functions to `U(n)`-finite functions.
The Haar probability measure of `U(n)` is invariant under it, which gives
`∫ a(κ g⁻¹) b(κ) dκ = ∫ a(twist(κ gᵀ)) b(twist κ) dκ`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexReverseTwist

open ComplexDuality Langlands.GeneralLinear

variable {n : ℕ}

/-! ## The antidiagonal permutation matrix -/

/-- The antidiagonal permutation matrix `w₀`. -/
def w0Mat (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = Fin.rev j then 1 else 0

theorem w0Mat_apply (i j : Fin n) : w0Mat n i j = if i = Fin.rev j then 1 else 0 := rfl

theorem w0Mat_mul_apply (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (w0Mat n * M) i j = M (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [w0Mat_apply]
  · intro b _ hb
    rw [w0Mat_apply, ite_eq_right, zero_mul]
    intro h
    exact hb (by rw [h, Fin.rev_rev])
  · simp

theorem mul_w0Mat_apply (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M * w0Mat n) i j = M i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [w0Mat_apply]
  · intro b _ hb
    rw [w0Mat_apply, ite_eq_right hb, mul_zero]
  · simp

theorem w0Mat_mul_mul_w0Mat_apply (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (w0Mat n * M * w0Mat n) i j = M (Fin.rev i) (Fin.rev j) := by
  rw [mul_w0Mat_apply, w0Mat_mul_apply]

theorem w0Mat_mul_self : w0Mat n * w0Mat n = 1 := by
  ext i j
  rw [w0Mat_mul_apply, w0Mat_apply, Matrix.one_apply]
  simp [Fin.rev_inj]

theorem w0Mat_transpose : (w0Mat n)ᵀ = w0Mat n := by
  ext i j
  rw [Matrix.transpose_apply, w0Mat_apply, w0Mat_apply]
  by_cases h : i = Fin.rev j
  · rw [ite_eq_left h, ite_eq_left (by rw [h, Fin.rev_rev])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', Fin.rev_rev]))]

theorem star_w0Mat : star (w0Mat n) = w0Mat n := by
  ext i j
  rw [Matrix.star_apply, w0Mat_apply, w0Mat_apply]
  by_cases h : j = Fin.rev i
  · rw [ite_eq_left h, ite_eq_left (by rw [h, Fin.rev_rev]), star_one]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', Fin.rev_rev])), star_zero]

/-- `w₀` as an element of `GL_n(ℂ)`. -/
def w0GL (n : ℕ) : Langlands.GeneralLinear n ℂ :=
  ⟨w0Mat n, w0Mat n, w0Mat_mul_self, w0Mat_mul_self⟩

theorem w0GL_val : ((w0GL n : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
    w0Mat n := rfl

theorem w0GL_mul_self : w0GL n * w0GL n = 1 :=
  Units.ext w0Mat_mul_self

theorem w0GL_inv : (w0GL n)⁻¹ = w0GL n :=
  inv_eq_of_mul_eq_one_right w0GL_mul_self

theorem w0GL_mem : w0GL n ∈ unitaryCompact ℂ n := by
  change w0Mat n ∈ Matrix.unitaryGroup (Fin n) ℂ
  rw [Matrix.mem_unitaryGroup_iff', star_w0Mat, w0Mat_mul_self]

/-! ## Transposition and the automorphism `g ↦ (gᵀ)⁻¹` -/

/-- The transpose of an invertible matrix. -/
def transposeGL (g : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ :=
  ⟨(g : Matrix (Fin n) (Fin n) ℂ)ᵀ, ((g⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem transposeGL_val (g : Langlands.GeneralLinear n ℂ) :
    ((transposeGL g : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (g : Matrix (Fin n) (Fin n) ℂ)ᵀ := rfl

theorem transposeGL_inv_val (g : Langlands.GeneralLinear n ℂ) :
    (((transposeGL g)⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((g⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ := rfl

theorem transposeGL_mul (g h : Langlands.GeneralLinear n ℂ) :
    transposeGL (g * h) = transposeGL h * transposeGL g :=
  Units.ext (by rw [Units.val_mul, transposeGL_val, transposeGL_val, transposeGL_val,
    Units.val_mul, Matrix.transpose_mul])

theorem transposeGL_transposeGL (g : Langlands.GeneralLinear n ℂ) :
    transposeGL (transposeGL g) = g :=
  Units.ext (by rw [transposeGL_val, transposeGL_val, Matrix.transpose_transpose])

theorem transposeGL_inv (g : Langlands.GeneralLinear n ℂ) :
    transposeGL g⁻¹ = (transposeGL g)⁻¹ :=
  Units.ext rfl

theorem transposeGL_w0GL : transposeGL (w0GL n) = w0GL n :=
  Units.ext (by rw [transposeGL_val, w0GL_val, w0Mat_transpose])

theorem continuous_transposeGL : Continuous (transposeGL (n := n)) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_transpose, Units.continuous_coe_inv.matrix_transpose⟩

theorem transposeGL_mem {g : Langlands.GeneralLinear n ℂ} (hg : g ∈ unitaryCompact ℂ n) :
    transposeGL g ∈ unitaryCompact ℂ n := by
  change (g : Matrix (Fin n) (Fin n) ℂ)ᵀ ∈ Matrix.unitaryGroup (Fin n) ℂ
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * star (g : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem hg
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, ← Matrix.transpose_mul,
    ← Matrix.star_eq_conjTranspose, h1, Matrix.transpose_one]

/-- The automorphism `g ↦ (gᵀ)⁻¹` of `GL_n(ℂ)`; on `U(n)` it is entrywise complex
conjugation. -/
def conjAut : Langlands.GeneralLinear n ℂ →* Langlands.GeneralLinear n ℂ where
  toFun g := (transposeGL g)⁻¹
  map_one' := by
    have : transposeGL (1 : Langlands.GeneralLinear n ℂ) = 1 :=
      Units.ext (by rw [transposeGL_val, Units.val_one, Matrix.transpose_one])
    rw [this, inv_one]
  map_mul' g h := by rw [transposeGL_mul, _root_.mul_inv_rev]

theorem conjAut_apply (g : Langlands.GeneralLinear n ℂ) : conjAut g = (transposeGL g)⁻¹ := rfl

theorem conjAut_conjAut (g : Langlands.GeneralLinear n ℂ) : conjAut (conjAut g) = g := by
  rw [conjAut_apply, conjAut_apply, transposeGL_inv, inv_inv, transposeGL_transposeGL]

theorem conjAut_transposeGL (g : Langlands.GeneralLinear n ℂ) :
    conjAut (transposeGL g) = g⁻¹ := by
  rw [conjAut_apply, transposeGL_transposeGL]

theorem conjAut_w0GL : conjAut (w0GL n) = w0GL n := by
  rw [conjAut_apply, transposeGL_w0GL, w0GL_inv]

theorem continuous_conjAut : Continuous (conjAut (n := n)) :=
  continuous_inv.comp continuous_transposeGL

theorem conjAut_mem {g : Langlands.GeneralLinear n ℂ} (hg : g ∈ unitaryCompact ℂ n) :
    conjAut g ∈ unitaryCompact ℂ n :=
  inv_mem (transposeGL_mem hg)

/-! ## The twist -/

/-- The twist `g ↦ w₀ (gᵀ)⁻¹`. -/
def twist (g : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ :=
  w0GL n * conjAut g

theorem twist_val (g : Langlands.GeneralLinear n ℂ) :
    ((twist g : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      w0Mat n * ((g⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ := rfl

theorem twist_mul (g h : Langlands.GeneralLinear n ℂ) : twist (g * h) = twist g * conjAut h := by
  rw [twist, twist, map_mul, mul_assoc]

theorem twist_twist (g : Langlands.GeneralLinear n ℂ) : twist (twist g) = g := by
  rw [twist, twist, map_mul, conjAut_w0GL, conjAut_conjAut, ← mul_assoc, w0GL_mul_self, one_mul]

theorem twist_one : twist (1 : Langlands.GeneralLinear n ℂ) = w0GL n := by
  rw [twist, map_one, mul_one]

theorem twist_mul_transposeGL (g h : Langlands.GeneralLinear n ℂ) :
    twist (g * transposeGL h) = twist g * h⁻¹ := by
  rw [twist_mul, conjAut_transposeGL]

theorem twist_mem {g : Langlands.GeneralLinear n ℂ} (hg : g ∈ unitaryCompact ℂ n) :
    twist g ∈ unitaryCompact ℂ n :=
  mul_mem w0GL_mem (conjAut_mem hg)

theorem continuous_twist : Continuous (twist (n := n)) :=
  continuous_const.mul continuous_conjAut

/-! ## Invariance of the Haar measure of `U(n)` -/

/-- `g ↦ (gᵀ)⁻¹` restricted to `U(n)`. -/
def conjK (n : ℕ) : unitaryCompact ℂ n →* unitaryCompact ℂ n where
  toFun k := ⟨conjAut (k : Langlands.GeneralLinear n ℂ), conjAut_mem k.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul conjAut _ _)

theorem conjK_val (k : unitaryCompact ℂ n) :
    ((conjK n k : unitaryCompact ℂ n) : Langlands.GeneralLinear n ℂ) =
      conjAut (k : Langlands.GeneralLinear n ℂ) := rfl

theorem continuous_conjK : Continuous (conjK n) :=
  continuous_induced_rng.mpr (continuous_conjAut.comp continuous_subtype_val)

theorem surjective_conjK : Function.Surjective (conjK n) := fun k =>
  ⟨conjK n k, Subtype.ext (by rw [conjK_val, conjK_val, conjAut_conjAut])⟩

theorem map_conjK_unitaryHaar : (unitaryHaar n).map (conjK n) = unitaryHaar n := by
  have : ((unitaryHaar n).map (conjK n)).IsHaarMeasure :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure _ (conjK n) continuous_conjK surjective_conjK
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- **Invariance of the Haar measure of `U(n)` under the twist.** -/
theorem integral_twist {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : Continuous F) :
    ∫ k : unitaryCompact ℂ n, F (twist (k : Langlands.GeneralLinear n ℂ)) ∂unitaryHaar n =
      ∫ k : unitaryCompact ℂ n, F (k : Langlands.GeneralLinear n ℂ) ∂unitaryHaar n := by
  set w : unitaryCompact ℂ n := ⟨w0GL n, w0GL_mem⟩
  set G : unitaryCompact ℂ n → ℂ := fun κ => F ((w * κ : unitaryCompact ℂ n) :
    Langlands.GeneralLinear n ℂ) with hG
  have hGc : Continuous G :=
    hF.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  have h1 : ∀ k : unitaryCompact ℂ n,
      F (twist (k : Langlands.GeneralLinear n ℂ)) = G (conjK n k) := fun k => rfl
  simp_rw [h1]
  rw [← integral_map continuous_conjK.measurable.aemeasurable hGc.aestronglyMeasurable,
    map_conjK_unitaryHaar]
  exact integral_mul_left_eq_self (fun κ : unitaryCompact ℂ n =>
    F (κ : Langlands.GeneralLinear n ℂ)) w

/-- **The twisted pairing identity.**
`∫ a(κ g⁻¹) b(κ) dκ = ∫ a(twist(κ gᵀ)) b(twist κ) dκ` for continuous `a`, `b`. -/
theorem integral_mul_inv_eq_twist {a b : Langlands.GeneralLinear n ℂ → ℂ} (ha : Continuous a)
    (hb : Continuous b) (g : Langlands.GeneralLinear n ℂ) :
    ∫ k : unitaryCompact ℂ n, a ((k : Langlands.GeneralLinear n ℂ) * g⁻¹) *
        b (k : Langlands.GeneralLinear n ℂ) ∂unitaryHaar n =
      ∫ k : unitaryCompact ℂ n, a (twist ((k : Langlands.GeneralLinear n ℂ) * transposeGL g)) *
        b (twist (k : Langlands.GeneralLinear n ℂ)) ∂unitaryHaar n := by
  simp_rw [twist_mul_transposeGL]
  exact (integral_twist (F := fun y => a (y * g⁻¹) * b y)
    ((ha.comp (continuous_id.mul continuous_const)).mul hb)).symm

/-! ## Twisting principal series -/

/-- Pullback along the twist. -/
def twistLin (n : ℕ) :
    (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) :=
  LinearMap.funLeft ℂ ℂ twist

theorem twistLin_apply (f : Langlands.GeneralLinear n ℂ → ℂ) (g : Langlands.GeneralLinear n ℂ) :
    twistLin n f g = f (twist g) := rfl

theorem twistLin_twistLin (f : Langlands.GeneralLinear n ℂ → ℂ) :
    twistLin n (twistLin n f) = f := by
  funext g
  rw [twistLin_apply, twistLin_apply, twist_twist]

theorem contMDiff_twistLin {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (twistLin n f) := by
  set ψ : Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun y => unitsExtension f (w0Mat n * (Ring.inverse y)ᵀ) with hψ
  refine contMDiff_of_contDiffOn (ψ := ψ) ?_ fun g => ?_
  · have hinv : ContDiffOn ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => w0Mat n * (Ring.inverse y)ᵀ)
        {y | IsUnit y} := by
      intro y hy
      obtain ⟨u, rfl⟩ := hy
      have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Matrix (Fin n) (Fin n) ℂ → _) u :=
        contDiffAt_ringInverse ℝ u
      have h2 : ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => w0Mat n * yᵀ :=
        ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ) (w0Mat n)).comp
          ((Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℂ).toContinuousLinearEquiv :
            Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)).contDiff
      exact (h2.contDiffAt.comp _ h1).contDiffWithinAt
    refine (contDiffOn_unitsExtension hf).comp hinv fun y hy => ?_
    obtain ⟨u, rfl⟩ := hy
    change IsUnit (w0Mat n * (Ring.inverse (u : Matrix (Fin n) (Fin n) ℂ))ᵀ)
    rw [Ring.inverse_unit]
    exact (Units.isUnit (twist u))
  · rw [twistLin_apply]
    simp only [hψ]
    rw [Ring.inverse_unit, ← twist_val, unitsExtension_val]

/-- `w₀ ((D⁻¹)ᵀ) w₀` for a diagonal `D`. -/
theorem w0_conj_diagonal (a : Fin n → ℂˣ) :
    w0GL n * conjAut (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * w0GL n =
      Iwasawa.diagonalUnits fun i => (a (Fin.rev i))⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, w0GL_val, conjAut_apply, transposeGL_inv_val, ← map_inv,
    Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, Matrix.diagonal_transpose]
  ext i j
  rw [w0Mat_mul_mul_w0Mat_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right (fun h' => h (Fin.rev_injective h')), ite_eq_right h]

/-- `w₀ ((U⁻¹)ᵀ) w₀` is upper unipotent for `U` upper unipotent. -/
theorem w0_conj_upperUnipotent (u : upperUnipotent n ℂ) :
    w0GL n * conjAut (u : Langlands.GeneralLinear n ℂ) * w0GL n ∈ upperUnipotent n ℂ := by
  have hv := (u⁻¹ : upperUnipotent n ℂ).2
  have hval : ((w0GL n * conjAut (u : Langlands.GeneralLinear n ℂ) * w0GL n :
      Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      w0Mat n * (((u⁻¹ : upperUnipotent n ℂ) : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ)ᵀ * w0Mat n := rfl
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change ((w0GL n * conjAut (u : Langlands.GeneralLinear n ℂ) * w0GL n :
      Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0
    rw [hval, w0Mat_mul_mul_w0Mat_apply, Matrix.transpose_apply]
    exact hv.1 (Fin.rev_lt_rev.mpr hij)
  · change ((w0GL n * conjAut (u : Langlands.GeneralLinear n ℂ) * w0GL n :
      Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1
    rw [hval, w0Mat_mul_mul_w0Mat_apply, Matrix.transpose_apply]
    exact hv.2 (Fin.rev i)

theorem twist_diagonal_mul (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    twist ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g) =
      (Iwasawa.diagonalUnits fun i => (a (Fin.rev i))⁻¹ : Langlands.GeneralLinear n ℂ) *
        ((⟨_, w0_conj_upperUnipotent u⟩ : upperUnipotent n ℂ) : Langlands.GeneralLinear n ℂ) *
          twist g := by
  rw [← w0_conj_diagonal]
  change w0GL n * conjAut (_ * _ * g) = _ * (w0GL n * conjAut (u : Langlands.GeneralLinear n ℂ) *
    w0GL n) * (w0GL n * conjAut g)
  rw [map_mul, map_mul]
  have h := w0GL_mul_self (n := n)
  simp only [mul_assoc]
  rw [← mul_assoc (w0GL n) (w0GL n), h, one_mul, ← mul_assoc (w0GL n) (w0GL n), h, one_mul]

theorem norm_inv_cpow (z : ℂˣ) (c : ℂ) :
    ((‖((z⁻¹ : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-c) = ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ c := by
  have hz : (0 : ℝ) ≤ ‖(z : ℂ)‖ ^ 2 := by positivity
  rw [Units.val_inv_eq_inv_val, norm_inv, inv_pow, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hz]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, inv_inv]

theorem principalSeriesCharacter_rev_inv {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ' : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n χ (fun i => (a (Fin.rev i))⁻¹) =
      principalSeriesCharacter ℂ n χ' a := by
  unfold principalSeriesCharacter
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Complex.finrank_real_complex]
  rw [hχ' j]
  congr 1
  have hrev : (((Fin.rev j : Fin n) : ℕ) : ℂ) = (n : ℂ) - 1 - (j : ℕ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hrev, show ((n : ℂ) - 1) / 2 - ((n : ℂ) - 1 - ((j : ℕ) : ℂ)) =
    -(((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) by ring, norm_inv_cpow]

/-- **Twisting the principal series.** If `χ'_j(z) = χ_{n-1-j}(z⁻¹)`, pullback along the twist
carries the principal series of `χ` to that of `χ'`. -/
theorem twistLin_mem_principalSeries {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ' : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ) :
    twistLin n f ∈ principalSeries ℂ n χ' := by
  refine ⟨contMDiff_twistLin hf.1, fun a u g => ?_⟩
  rw [twistLin_apply, twistLin_apply, twist_diagonal_mul, hf.2,
    principalSeriesCharacter_rev_inv hχ']

theorem rightTranslation_twistLin (f : Langlands.GeneralLinear n ℂ → ℂ)
    (k : Langlands.GeneralLinear n ℂ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k (twistLin n f) =
      twistLin n (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (conjAut k) f) := by
  funext g
  change f (twist (g * k)) = f (twist g * conjAut k)
  rw [twist_mul]

/-- **Twisting `U(n)`-finite functions.** -/
theorem twistLin_mem_kFiniteFunctions {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ' : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    twistLin n f ∈ kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n) := by
  refine ⟨twistLin_mem_principalSeries hχ' hf.1, ?_⟩
  refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
        f)) := (mem_kFiniteVectors_iff _ _ _).mp hf.2
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range
    fun k : unitaryCompact ℂ n => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
      (k : Langlands.GeneralLinear n ℂ) f)).map (twistLin n)) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨_, Submodule.subset_span ⟨conjK n k, rfl⟩, ?_⟩
  dsimp only
  rw [rightTranslation_twistLin, conjK_val]

end ComplexReverseTwist

end Langlands.Archimedean
