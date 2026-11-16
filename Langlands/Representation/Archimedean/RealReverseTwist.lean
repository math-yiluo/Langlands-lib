import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-!
# The twist `g ↦ w₀ (gᵀ)⁻¹` of `GL_n(ℝ)` and principal series

`twist g = w₀ (gᵀ)⁻¹`, with `w₀` the antidiagonal permutation matrix, is an involution of
`GL_n(ℝ)` with `twist (g h) = twist g · (hᵀ)⁻¹`; on `O(n)` it is left multiplication by `w₀`.
Pulling back along it carries the principal series of characters `χ_l` to that of
`x ↦ χ_{n-1-l}(x⁻¹)` and `O(n)`-finite functions to `O(n)`-finite functions; it commutes with
right translation by `O(n)` and turns the right derivative along `Y` into the right derivative
along `-Yᵀ`. The invariance of the Haar measure of `O(n)` gives
`∫ a(κ g⁻¹) b(κ) dκ = ∫ a(twist(κ gᵀ)) b(twist κ) dκ`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealReverseTwist

open RealPrincipalSeriesDuality Langlands.GeneralLinear

attribute [local instance] measurableSpaceK

/-- Borel structure on `O(n)` (its measurable space is the Borel one). -/
local instance borelSpaceK_tw (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

/-! ## The antidiagonal permutation matrix -/

/-- The antidiagonal permutation matrix `w₀`. -/
def w0Mat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = Fin.rev j then 1 else 0

theorem w0Mat_apply (i j : Fin n) : w0Mat n i j = if i = Fin.rev j then 1 else 0 := rfl

theorem w0Mat_mul_apply (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (w0Mat n * M) i j = M (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [w0Mat_apply]
  · intro b _ hb
    rw [w0Mat_apply, ite_eq_right, zero_mul]
    intro h
    exact hb (by rw [h, Fin.rev_rev])
  · simp

theorem mul_w0Mat_apply (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (M * w0Mat n) i j = M i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [w0Mat_apply]
  · intro b _ hb
    rw [w0Mat_apply, ite_eq_right hb, mul_zero]
  · simp

theorem w0Mat_mul_mul_w0Mat_apply (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
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

/-- `w₀` as an element of `GL_n(ℝ)`. -/
def w0GL (n : ℕ) : Langlands.GeneralLinear n ℝ :=
  ⟨w0Mat n, w0Mat n, w0Mat_mul_self, w0Mat_mul_self⟩

theorem w0GL_val : ((w0GL n : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
    w0Mat n := rfl

theorem w0GL_mul_self : w0GL n * w0GL n = 1 :=
  Units.ext w0Mat_mul_self

theorem w0GL_inv : (w0GL n)⁻¹ = w0GL n :=
  inv_eq_of_mul_eq_one_right w0GL_mul_self

theorem w0GL_mem : w0GL n ∈ unitaryCompact ℝ n := by
  change w0Mat n ∈ Matrix.unitaryGroup (Fin n) ℝ
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, w0Mat_transpose, w0Mat_mul_self]

/-! ## Transposition and the automorphism `g ↦ (gᵀ)⁻¹` -/

/-- The transpose `g ↦ gᵀ` on `GL_n(ℝ)`. -/
def transposeGL (g : Langlands.GeneralLinear n ℝ) : Langlands.GeneralLinear n ℝ where
  val := (g : Matrix (Fin n) (Fin n) ℝ)ᵀ
  inv := ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem transposeGL_val (g : Langlands.GeneralLinear n ℝ) :
    ((transposeGL g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      (g : Matrix (Fin n) (Fin n) ℝ)ᵀ := rfl

theorem transposeGL_inv_val (g : Langlands.GeneralLinear n ℝ) :
    (((transposeGL g)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := rfl

theorem transposeGL_mul (g h : Langlands.GeneralLinear n ℝ) :
    transposeGL (g * h) = transposeGL h * transposeGL g :=
  Units.ext (by rw [Units.val_mul, transposeGL_val, transposeGL_val, transposeGL_val,
    Units.val_mul, Matrix.transpose_mul])

theorem transposeGL_one : transposeGL (1 : Langlands.GeneralLinear n ℝ) = 1 :=
  Units.ext (by rw [transposeGL_val, Units.val_one, Matrix.transpose_one])

theorem transposeGL_transposeGL (g : Langlands.GeneralLinear n ℝ) :
    transposeGL (transposeGL g) = g :=
  Units.ext (by rw [transposeGL_val, transposeGL_val, Matrix.transpose_transpose])

theorem transposeGL_inv (g : Langlands.GeneralLinear n ℝ) :
    transposeGL g⁻¹ = (transposeGL g)⁻¹ :=
  Units.ext rfl

theorem transposeGL_w0GL : transposeGL (w0GL n) = w0GL n :=
  Units.ext (by rw [transposeGL_val, w0GL_val, w0Mat_transpose])

/-- On `O(n)` the transpose is the inverse. -/
theorem transposeGL_of_mem {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    transposeGL k = k⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  rw [Units.val_mul, transposeGL_val, Units.val_one]
  exact transpose_mul_self_of_mem ⟨k, hk⟩

/-- The automorphism `g ↦ (gᵀ)⁻¹` of `GL_n(ℝ)`. -/
def conjAut : Langlands.GeneralLinear n ℝ →* Langlands.GeneralLinear n ℝ where
  toFun g := (transposeGL g)⁻¹
  map_one' := by rw [transposeGL_one, inv_one]
  map_mul' g h := by rw [transposeGL_mul, _root_.mul_inv_rev]

theorem conjAut_apply (g : Langlands.GeneralLinear n ℝ) : conjAut g = (transposeGL g)⁻¹ := rfl

theorem conjAut_conjAut (g : Langlands.GeneralLinear n ℝ) : conjAut (conjAut g) = g := by
  rw [conjAut_apply, conjAut_apply, transposeGL_inv, inv_inv, transposeGL_transposeGL]

theorem conjAut_transposeGL (g : Langlands.GeneralLinear n ℝ) :
    conjAut (transposeGL g) = g⁻¹ := by
  rw [conjAut_apply, transposeGL_transposeGL]

theorem conjAut_w0GL : conjAut (w0GL n) = w0GL n := by
  rw [conjAut_apply, transposeGL_w0GL, w0GL_inv]

/-- `g ↦ (gᵀ)⁻¹` is the identity on `O(n)`. -/
theorem conjAut_of_mem {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    conjAut k = k := by
  rw [conjAut_apply, transposeGL_of_mem hk, inv_inv]

/-- `g ↦ (gᵀ)⁻¹` on the one-parameter subgroup `s ↦ exp(s Y)` gives `s ↦ exp(s (-Yᵀ))`. -/
theorem conjAut_matrixExpUnit (Y : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    conjAut (matrixExpUnit n (s • Y)) = matrixExpUnit n (s • -Yᵀ) := by
  apply Units.ext
  rw [conjAut_apply, transposeGL_inv_val, matrixExpUnit_val]
  change (NormedSpace.exp (-(s • Y)))ᵀ = _
  rw [← Matrix.exp_transpose, Matrix.transpose_neg, Matrix.transpose_smul, smul_neg]

/-! ## The twist -/

/-- The twist `g ↦ w₀ (gᵀ)⁻¹`. -/
def twist (g : Langlands.GeneralLinear n ℝ) : Langlands.GeneralLinear n ℝ :=
  w0GL n * conjAut g

theorem twist_mul (g h : Langlands.GeneralLinear n ℝ) : twist (g * h) = twist g * conjAut h := by
  rw [twist, twist, map_mul, mul_assoc]

theorem twist_twist (g : Langlands.GeneralLinear n ℝ) : twist (twist g) = g := by
  rw [twist, twist, map_mul, conjAut_w0GL, conjAut_conjAut, ← mul_assoc, w0GL_mul_self, one_mul]

theorem twist_one : twist (1 : Langlands.GeneralLinear n ℝ) = w0GL n := by
  rw [twist, map_one, mul_one]

theorem twist_mul_transposeGL (g h : Langlands.GeneralLinear n ℝ) :
    twist (g * transposeGL h) = twist g * h⁻¹ := by
  rw [twist_mul, conjAut_transposeGL]

/-- On `O(n)` the twist is left multiplication by `w₀`. -/
theorem twist_of_mem {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    twist k = w0GL n * k := by
  rw [twist, conjAut_of_mem hk]

/-! ## Invariance of the Haar measure of `O(n)` -/

/-- **The twisted pairing identity.** `∫ a(κ g⁻¹) b(κ) dκ = ∫ a(twist(κ gᵀ)) b(twist κ) dκ`. -/
theorem integral_mul_inv_eq_twist (a b : Langlands.GeneralLinear n ℝ → ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    ∫ κ : unitaryCompact ℝ n, a ((κ : Langlands.GeneralLinear n ℝ) * g⁻¹) *
        b (κ : Langlands.GeneralLinear n ℝ) ∂haarK n =
      ∫ κ : unitaryCompact ℝ n, a (twist ((κ : Langlands.GeneralLinear n ℝ) * transposeGL g)) *
        b (twist (κ : Langlands.GeneralLinear n ℝ)) ∂haarK n := by
  have h : ∀ κ : unitaryCompact ℝ n,
      a (twist ((κ : Langlands.GeneralLinear n ℝ) * transposeGL g)) *
        b (twist (κ : Langlands.GeneralLinear n ℝ)) =
      (fun κ' : unitaryCompact ℝ n => a ((κ' : Langlands.GeneralLinear n ℝ) * g⁻¹) *
        b (κ' : Langlands.GeneralLinear n ℝ)) (⟨w0GL n, w0GL_mem⟩ * κ) := fun κ => by
    rw [twist_mul_transposeGL, twist_of_mem κ.2]
    rfl
  simp_rw [h]
  exact (integral_mul_left_eq_self (fun κ' : unitaryCompact ℝ n =>
    a ((κ' : Langlands.GeneralLinear n ℝ) * g⁻¹) * b (κ' : Langlands.GeneralLinear n ℝ)) _).symm

/-! ## Twisting functions -/

/-- Pullback along the twist. -/
def twistLin (n : ℕ) :
    (Langlands.GeneralLinear n ℝ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear n ℝ → ℂ) :=
  LinearMap.funLeft ℂ ℂ twist

theorem twistLin_apply (f : Langlands.GeneralLinear n ℝ → ℂ) (g : Langlands.GeneralLinear n ℝ) :
    twistLin n f g = f (twist g) := rfl

theorem twistLin_twistLin (f : Langlands.GeneralLinear n ℝ → ℂ) :
    twistLin n (twistLin n f) = f := by
  funext g
  rw [twistLin_apply, twistLin_apply, twist_twist]

theorem contMDiff_twistLin {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (twistLin n f) := by
  set ψ : Matrix (Fin n) (Fin n) ℝ → ℂ :=
    fun y => unitsExtension f (w0Mat n * (Ring.inverse y)ᵀ) with hψ
  refine contMDiff_of_contDiffOn (ψ := ψ) ?_ fun g => ?_
  · have hinv : ContDiffOn ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => w0Mat n * (Ring.inverse y)ᵀ)
        {y | IsUnit y} := by
      intro y hy
      obtain ⟨u, rfl⟩ := hy
      have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Matrix (Fin n) (Fin n) ℝ → _) u :=
        contDiffAt_ringInverse ℝ u
      have h2 : ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℝ => w0Mat n * yᵀ :=
        ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) (w0Mat n)).comp
          ((Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv :
            Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ)).contDiff
      exact (h2.contDiffAt.comp _ h1).contDiffWithinAt
    refine (contDiffOn_unitsExtension hf).comp hinv fun y hy => ?_
    obtain ⟨u, rfl⟩ := hy
    change IsUnit (w0Mat n * (Ring.inverse (u : Matrix (Fin n) (Fin n) ℝ))ᵀ)
    rw [Ring.inverse_unit]
    exact Units.isUnit (twist u)
  · rw [twistLin_apply]
    simp only [hψ]
    rw [Ring.inverse_unit]
    exact (unitsExtension_val f (twist g)).symm

/-! ## Twisting principal series -/

/-- `w₀ ((D⁻¹)ᵀ) w₀` for a diagonal `D`. -/
theorem w0_conj_diagonal (a : Fin n → ℝˣ) :
    w0GL n * conjAut (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) * w0GL n =
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
theorem w0_conj_upperUnipotent (u : upperUnipotent n ℝ) :
    w0GL n * conjAut (u : Langlands.GeneralLinear n ℝ) * w0GL n ∈ upperUnipotent n ℝ := by
  have hv := (u⁻¹ : upperUnipotent n ℝ).2
  have hval : ((w0GL n * conjAut (u : Langlands.GeneralLinear n ℝ) * w0GL n :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      w0Mat n * (((u⁻¹ : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ)ᵀ * w0Mat n := rfl
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change ((w0GL n * conjAut (u : Langlands.GeneralLinear n ℝ) * w0GL n :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i j = 0
    rw [hval, w0Mat_mul_mul_w0Mat_apply, Matrix.transpose_apply]
    exact hv.1 (Fin.rev_lt_rev.mpr hij)
  · change ((w0GL n * conjAut (u : Langlands.GeneralLinear n ℝ) * w0GL n :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i i = 1
    rw [hval, w0Mat_mul_mul_w0Mat_apply, Matrix.transpose_apply]
    exact hv.2 (Fin.rev i)

theorem twist_diagonal_mul (a : Fin n → ℝˣ) (u : upperUnipotent n ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    twist ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * g) =
      (Iwasawa.diagonalUnits fun i => (a (Fin.rev i))⁻¹ : Langlands.GeneralLinear n ℝ) *
        ((⟨_, w0_conj_upperUnipotent u⟩ : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) *
          twist g := by
  rw [← w0_conj_diagonal]
  change w0GL n * conjAut (_ * _ * g) = _ * (w0GL n * conjAut (u : Langlands.GeneralLinear n ℝ) *
    w0GL n) * (w0GL n * conjAut g)
  rw [map_mul, map_mul]
  have h := w0GL_mul_self (n := n)
  simp only [mul_assoc]
  rw [← mul_assoc (w0GL n) (w0GL n), h, one_mul, ← mul_assoc (w0GL n) (w0GL n), h, one_mul]

theorem norm_inv_cpow (z : ℝˣ) (c : ℂ) :
    ((‖((z⁻¹ : ℝˣ) : ℝ)‖ : ℝ) : ℂ) ^ (-c) = ((‖(z : ℝ)‖ : ℝ) : ℂ) ^ c := by
  have hz : (0 : ℝ) ≤ ‖(z : ℝ)‖ := norm_nonneg _
  rw [Units.val_inv_eq_inv_val, norm_inv, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hz]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, inv_inv]

theorem principalSeriesCharacter_rev_inv {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin n) (z : ℝˣ), χ' j z = χ (Fin.rev j) z⁻¹) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n χ (fun i => (a (Fin.rev i))⁻¹) =
      principalSeriesCharacter ℝ n χ' a := by
  unfold principalSeriesCharacter
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Module.finrank_self, pow_one]
  rw [hχ' j]
  congr 1
  have hrev : (((Fin.rev j : Fin n) : ℕ) : ℂ) = (n : ℂ) - 1 - (j : ℕ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hrev, show ((n : ℂ) - 1) / 2 - ((n : ℂ) - 1 - ((j : ℕ) : ℂ)) =
    -(((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) by ring, norm_inv_cpow]

/-- **Twisting the principal series.** If `χ'_j(x) = χ_{n-1-j}(x⁻¹)`, pullback along the twist
carries the principal series of `χ` to that of `χ'`. -/
theorem twistLin_mem_principalSeries {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin n) (z : ℝˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n χ) :
    twistLin n f ∈ principalSeries ℝ n χ' := by
  refine ⟨contMDiff_twistLin hf.1, fun a u g => ?_⟩
  rw [twistLin_apply, twistLin_apply, twist_diagonal_mul, hf.2,
    principalSeriesCharacter_rev_inv hχ']

/-- Right translation by `k ∈ O(n)` commutes with the twist. -/
theorem rightTranslation_twistLin (f : Langlands.GeneralLinear n ℝ → ℂ)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k (twistLin n f) =
      twistLin n (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f) := by
  funext g
  change f (twist (g * k)) = f (twist g * k)
  rw [twist_mul, conjAut_of_mem hk]

/-- **Twisting `O(n)`-finite functions.** -/
theorem twistLin_mem_kFiniteFunctions {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin n) (z : ℝˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) :
    twistLin n f ∈ kFiniteFunctions (principalSeries ℝ n χ') (unitaryCompact ℝ n) := by
  refine ⟨twistLin_mem_principalSeries hχ' hf.1, ?_⟩
  refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
        f)) := (mem_kFiniteVectors_iff _ _ _).mp hf.2
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range
    fun k : unitaryCompact ℝ n => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (k : Langlands.GeneralLinear n ℝ) f)).map (twistLin n)) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  exact (rightTranslation_twistLin f k.2).symm

/-- **Right derivatives of twisted functions.** `R(Y)(f ∘ twist) = (R(-Yᵀ) f) ∘ twist`. -/
theorem rightDerivative_twistLin {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (Y : Matrix (Fin n) (Fin n) ℝ) :
    rightDerivative (matrixModel ℝ n) Y (twistLin n f) =
      twistLin n (rightDerivative (matrixModel ℝ n) (-Yᵀ) f) := by
  funext g
  have h1 := hasDerivAt_mul_matrixExpUnit_smul ((contMDiff_twistLin hf).of_le (by norm_num)) g Y
  have h2 := hasDerivAt_mul_matrixExpUnit_smul (hf.of_le (by norm_num)) (twist g) (-Yᵀ)
  refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_))
  change f (twist (g * matrixExpUnit n (s • Y))) = f (twist g * matrixExpUnit n (s • -Yᵀ))
  rw [twist_mul, conjAut_matrixExpUnit]

end RealReverseTwist

end Langlands.Archimedean
