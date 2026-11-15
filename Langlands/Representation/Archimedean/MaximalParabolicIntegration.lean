import Langlands.Representation.Archimedean.KIntegralInvariance
import Langlands.Representation.Archimedean.OrthogonalLastRowIntegral
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# The `O(n)`-integral in coordinates of the maximal parabolic subgroup `P_{n-1,1}`
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace MaximalParabolicIntegration

variable {m : ℕ}

/-! ## Block matrices for `P_{m,1}` -/

/-- `ι(A) = diag(A, 1)`. -/
def iota (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

@[simp] theorem iota_last_last (A : Matrix (Fin m) (Fin m) ℝ) :
    iota A (Fin.last m) (Fin.last m) = 1 := by simp [iota]

@[simp] theorem iota_last_castSucc (A : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    iota A (Fin.last m) j.castSucc = 0 := by simp [iota]

@[simp] theorem iota_castSucc_last (A : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    iota A i.castSucc (Fin.last m) = 0 := by simp [iota]

@[simp] theorem iota_castSucc_castSucc (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    iota A i.castSucc j.castSucc = A i j := by simp [iota]

theorem iota_mul (A B : Matrix (Fin m) (Fin m) ℝ) : iota (A * B) = iota A * iota B := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem iota_one : iota (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem iota_transpose (A : Matrix (Fin m) (Fin m) ℝ) : (iota A)ᵀ = iota Aᵀ := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp

theorem det_iota (A : Matrix (Fin m) (Fin m) ℝ) : (iota A).det = A.det := by
  rw [Matrix.det_succ_column (iota A) (Fin.last m)]
  rw [Fin.sum_univ_castSucc]
  simp only [iota_castSucc_last, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    iota_last_last]
  have : (iota A).submatrix (Fin.last m).succAbove (Fin.last m).succAbove = A := by
    ext i j
    simp [Fin.succAbove_last]
  rw [this]
  simp

/-- `d(a) = diag(1, …, 1, a)`. -/
def dlast (a : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.diagonal fun i => Fin.lastCases a (fun _ => 1) i

theorem iota_mul_dlast (A : Matrix (Fin m) (Fin m) ℝ) (a : ℝ) :
    iota A * dlast a = dlast a * iota A := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [dlast, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- `n(c)`: the identity with the column `c` above the last diagonal entry. -/
def nP (c : Fin m → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (c i') (fun j' => if i' = j' then 1 else 0) j) i

theorem iota_mul_nP (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) :
    iota A * nP c = nP (A *ᵥ c) * iota A := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [nP, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]

theorem nP_isUpperTriangular (c : Fin m → ℝ) : (nP c).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  have hj : j ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last i))
  obtain ⟨j', rfl⟩ : ∃ j', j = j'.castSucc := ⟨j.castPred hj, by simp⟩
  induction i using Fin.lastCases with
  | last => simp [nP]
  | cast i' =>
    have hne : i' ≠ j' := fun h => by
      subst h
      exact lt_irrefl _ hij
    simp [nP, hne]

theorem nP_diag (c : Fin m → ℝ) (i : Fin (m + 1)) : nP c i i = 1 := by
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp [nP]

theorem det_nP (c : Fin m → ℝ) : (nP c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (nP_isUpperTriangular c)]
  simp [nP_diag]

theorem det_dlast (a : ℝ) : (dlast (m := m) a).det = a := by
  rw [dlast, Matrix.det_diagonal, Fin.prod_univ_castSucc]
  simp

/-- The top-left block. -/
def topLeft (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => p i.castSucc j.castSucc

/-- **Decomposition in `P_{m,1}`.** A matrix with last row `(0, …, 0, a)`, `a ≠ 0`, is
`n(c) · ι(A) · d(a)`. -/
theorem eq_nP_mul_iota_mul_dlast {p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hp : ∀ j : Fin m, p (Fin.last m) j.castSucc = 0) (ha : p (Fin.last m) (Fin.last m) ≠ 0) :
    p = nP (fun i => p i.castSucc (Fin.last m) / p (Fin.last m) (Fin.last m)) *
      iota (topLeft p) * dlast (p (Fin.last m) (Fin.last m)) := by
  ext i j
  simp only [dlast, Matrix.mul_diagonal]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [nP, iota, Matrix.mul_apply, Fin.sum_univ_castSucc]
  · simp [nP, iota, Matrix.mul_apply, Fin.sum_univ_castSucc, hp]
  · simp [nP, iota, Matrix.mul_apply, Fin.sum_univ_castSucc]
    field_simp
  · simp [nP, iota, topLeft, Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem det_eq_mul_det_topLeft {p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hp : ∀ j : Fin m, p (Fin.last m) j.castSucc = 0) (ha : p (Fin.last m) (Fin.last m) ≠ 0) :
    p.det = p (Fin.last m) (Fin.last m) * (topLeft p).det := by
  conv_lhs => rw [eq_nP_mul_iota_mul_dlast hp ha]
  rw [Matrix.det_mul, Matrix.det_mul, det_nP, det_iota, det_dlast]
  ring

/-! ## The modulus character -/

/-- The modulus character `diag(a) ↦ ∏ᵢ |aᵢ|^(n-1-2i)` of the upper triangular Borel subgroup. -/
def modulusCharacter (n : ℕ) (a : Fin n → ℝˣ) : ℂ :=
  ∏ i : Fin n, ((|(a i : ℝ)| : ℝ) : ℂ) ^ (((n : ℂ) - 1) - 2 * ((i : ℕ) : ℂ))

/-- `F` transforms on the left by the modulus character of the upper triangular Borel subgroup. -/
def IsModulusCovariant {n : ℕ} (F : Langlands.GeneralLinear n ℝ → ℂ) : Prop :=
  ∀ (a : Fin n → ℝˣ) (u : Langlands.GeneralLinear.upperUnipotent n ℝ)
    (g : Langlands.GeneralLinear n ℝ),
    F ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * g) = modulusCharacter n a * F g

theorem isModulusEquivariant_of_covariant {n : ℕ} {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : IsModulusCovariant F) : RealPrincipalSeriesDuality.IsModulusEquivariant F := by
  intro x u g
  rw [RealPrincipalSeriesDuality.matrixExpUnit_diagonal, hF]
  congr 1
  rw [modulusCharacter, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_mk0, abs_of_pos (Real.exp_pos _), RealPrincipalSeriesDuality.ofReal_exp_cpow,
    RealPrincipalSeriesDuality.modulusExponent]
  ring_nf

theorem modulusCharacter_one {n : ℕ} : modulusCharacter n (fun _ => 1) = 1 := by
  simp [modulusCharacter]

theorem covariant_upperUnipotent {n : ℕ} {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : IsModulusCovariant F) (u : Langlands.GeneralLinear.upperUnipotent n ℝ)
    (g : Langlands.GeneralLinear n ℝ) : F ((u : Langlands.GeneralLinear n ℝ) * g) = F g := by
  have := hF (fun _ => 1) u g
  have h1 : (Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin n => (1 : ℝˣ)) :
      Langlands.GeneralLinear n ℝ) = 1 := map_one _
  rw [h1, one_mul, modulusCharacter_one, one_mul] at this
  exact this

/-! ## The Levi embedding on `GL` -/

/-- `ι` as a monoid homomorphism of matrices. -/
def iotaHom : Matrix (Fin m) (Fin m) ℝ →* Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ where
  toFun := iota
  map_one' := iota_one
  map_mul' := iota_mul

/-- `g ↦ diag(g, 1)` from `GL_m(ℝ)` to `GL_{m+1}(ℝ)`. -/
def iotaGL : Langlands.GeneralLinear m ℝ →* Langlands.GeneralLinear (m + 1) ℝ :=
  Units.map iotaHom

@[simp] theorem iotaGL_val (g : Langlands.GeneralLinear m ℝ) :
    ((iotaGL g : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      iota (g : Matrix (Fin m) (Fin m) ℝ) := rfl

theorem iotaGL_mem_unitaryCompact {k : Langlands.GeneralLinear m ℝ} (hk : k ∈ unitaryCompact ℝ m) :
    iotaGL k ∈ unitaryCompact ℝ (m + 1) := by
  change iota (k : Matrix (Fin m) (Fin m) ℝ) ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ
  have hk' := Matrix.mem_unitaryGroup_iff.mp hk
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, iota_transpose, ← iota_mul]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hk'
  rw [hk', iota_one]

/-- `ι` on `O(m)`. -/
def iotaK (k : unitaryCompact ℝ m) : unitaryCompact ℝ (m + 1) :=
  ⟨iotaGL (k : Langlands.GeneralLinear m ℝ), iotaGL_mem_unitaryCompact k.2⟩

theorem iotaGL_mem_upperUnipotent (u : Langlands.GeneralLinear.upperUnipotent m ℝ) :
    iotaGL (u : Langlands.GeneralLinear m ℝ) ∈ Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change j < i at hij
    change iota ((u : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i j = 0
    have hj : j ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last i))
    obtain ⟨j', rfl⟩ : ∃ j', j = j'.castSucc := ⟨j.castPred hj, by simp⟩
    induction i using Fin.lastCases with
    | last => simp
    | cast i' =>
      rw [iota_castSucc_castSucc]
      exact u.2.1 (Fin.castSucc_lt_castSucc_iff.mp hij)
  · change iota ((u : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i i = 1
    induction i using Fin.lastCases with
    | last => simp
    | cast i' =>
      rw [iota_castSucc_castSucc]
      exact u.2.2 i'

theorem iotaGL_diagonalUnits (a : Fin m → ℝˣ) :
    iotaGL (Langlands.GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℝ) =
      Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => Fin.lastCases 1 a i) := by
  apply Units.ext
  rw [iotaGL_val, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val,
    Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.diagonal_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem modulusCharacter_lastCases (a : Fin m → ℝˣ) :
    modulusCharacter (m + 1) (fun i => Fin.lastCases 1 a i) =
      modulusCharacter m a * ∏ i : Fin m, ((|(a i : ℝ)| : ℝ) : ℂ) := by
  rw [modulusCharacter, Fin.prod_univ_castSucc, modulusCharacter, ← Finset.prod_mul_distrib]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Units.val_one, abs_one,
    Complex.ofReal_one, Complex.one_cpow, mul_one, Fin.val_castSucc]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha : ((|(a i : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (a i).ne_zero
  have hexp : (((m + 1 : ℕ) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) =
      ((m : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) + 1 := by
    push_cast
    ring
  rw [hexp, Complex.cpow_add _ _ ha, Complex.cpow_one]

/-! ## The Levi slice -/

theorem det_upperUnipotent {n : ℕ} (u : Langlands.GeneralLinear.upperUnipotent n ℝ) :
    ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular u.2.1]
  exact Finset.prod_eq_one fun i _ => u.2.2 i

/-- The Levi slice `g ↦ F(ι(g) y) |det g|⁻¹` on `GL_m(ℝ)`. -/
def leviSlice (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ) (y : Langlands.GeneralLinear (m + 1) ℝ)
    (g : Langlands.GeneralLinear m ℝ) : ℂ :=
  F (iotaGL g * y) * ((|(g : Matrix (Fin m) (Fin m) ℝ).det| : ℝ) : ℂ)⁻¹

theorem leviSlice_covariant {F : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hF : IsModulusCovariant F) (y : Langlands.GeneralLinear (m + 1) ℝ) :
    IsModulusCovariant (leviSlice F y) := by
  intro a u g
  have hu := iotaGL_mem_upperUnipotent u
  have h1 : iotaGL ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℝ) *
      (u : Langlands.GeneralLinear m ℝ) * g) * y =
      (Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => Fin.lastCases 1 a i) :
        Langlands.GeneralLinear (m + 1) ℝ) *
        ((⟨iotaGL (u : Langlands.GeneralLinear m ℝ), hu⟩ :
          Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ) : Langlands.GeneralLinear (m + 1) ℝ) *
        (iotaGL g * y) := by
    rw [map_mul, map_mul, iotaGL_diagonalUnits]
    simp only [mul_assoc]
  have hdet : ((((Langlands.GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℝ) *
      (u : Langlands.GeneralLinear m ℝ) * g : Langlands.GeneralLinear m ℝ) :
        Matrix (Fin m) (Fin m) ℝ).det) =
      (∏ i, (a i : ℝ)) * ((g : Matrix (Fin m) (Fin m) ℝ).det) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_upperUnipotent,
      Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.det_diagonal, mul_one]
  unfold leviSlice
  rw [h1, hF, hdet, modulusCharacter_lastCases, abs_mul, Finset.abs_prod, Complex.ofReal_mul,
    Complex.ofReal_prod]
  have hne : (∏ i : Fin m, ((|(a i : ℝ)| : ℝ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast abs_ne_zero.mpr (a i).ne_zero
  rw [mul_inv]
  field_simp

/-- `ι` as an affine map of matrices: `ι(Y) = L(Y) + ι(0)`. -/
def iotaLin : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ where
  toFun Y := Matrix.of fun i j => Fin.lastCases 0 (fun i' => Fin.lastCases 0 (fun j' => Y i' j') j) i
  map_add' Y Y' := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp
  map_smul' c Y := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp

theorem iota_eq_iotaLin_add (Y : Matrix (Fin m) (Fin m) ℝ) : iota Y = iotaLin Y + iota 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [iotaLin]

theorem contDiff_iota : ContDiff ℝ ∞ (iota (m := m)) := by
  have h : (iota (m := m)) = fun Y => (LinearMap.toContinuousLinearMap iotaLin) Y + iota 0 :=
    funext fun Y => by rw [iota_eq_iotaLin_add]; rfl
  rw [h]
  exact (LinearMap.toContinuousLinearMap iotaLin).contDiff.add contDiff_const

theorem contMDiff_leviSlice {F : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hFs : ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ F) (y : Langlands.GeneralLinear (m + 1) ℝ) :
    ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ (leviSlice F y) := by
  set ψ : Matrix (Fin m) (Fin m) ℝ → ℂ := fun Y =>
    unitsExtension F (iota Y * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *
      ((|Y.det| : ℝ) : ℂ)⁻¹ with hψ
  refine contMDiff_of_contDiffOn (ψ := ψ) ?_ fun g => ?_
  · intro Y hY
    have hY' : IsUnit Y := hY
    have hdet : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY').ne_zero
    refine ContDiffAt.contDiffWithinAt (ContDiffAt.mul ?_ ?_)
    · have hmul : ContDiff ℝ ∞ fun Y : Matrix (Fin m) (Fin m) ℝ =>
          iota Y * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
        contDiff_iota.mul contDiff_const
      have hunit : IsUnit (iota Y * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) := by
        rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, det_iota]
        exact (isUnit_iff_ne_zero.mpr hdet).mul (Matrix.isUnit_iff_isUnit_det _ |>.mp (Units.isUnit y))
      exact ((contDiffOn_unitsExtension hFs).contDiffAt
        (isOpen_setOf_isUnit_matrix.mem_nhds hunit)).comp Y hmul.contDiffAt
    · have hd : ContDiff ℝ ∞ fun Y : Matrix (Fin m) (Fin m) ℝ => Y.det :=
        PrincipalSeriesExtension.contDiff_det_comp fun p q => PrincipalSeriesExtension.contDiff_entry p q
      have habs : ContDiffAt ℝ ∞ (fun Y : Matrix (Fin m) (Fin m) ℝ => |Y.det|) Y :=
        (contDiffAt_abs hdet).comp Y hd.contDiffAt
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp Y
        (habs.inv (abs_ne_zero.mpr hdet)) |>.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun Z => by simp)
  · simp only [hψ, leviSlice]
    rw [← iotaGL_val, ← Units.val_mul, unitsExtension_val]

/-! ## The `O(m)`-average -/

section Natural

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK_mpi (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-- `F^♮(x) = ∫_{O(m)} F(ι(k) x) dk`. -/
def natural (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ) (x : Langlands.GeneralLinear (m + 1) ℝ) :
    ℂ :=
  ∫ k : unitaryCompact ℝ m, F (iotaGL (k : Langlands.GeneralLinear m ℝ) * x) ∂haarK m

theorem abs_det_unitary {n : ℕ} (k : unitaryCompact ℝ n) :
    |((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).det| = 1 := by
  have h := congrArg Matrix.det (OrthogonalLastRowIntegral.mul_transpose_eq_one k)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have h2 : ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).det ^ 2 = 1 := by
    rw [sq]
    exact h
  rcases sq_eq_one_iff.mp h2 with h3 | h3 <;> simp [h3]

variable {F : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
  (hFs : ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ F) (hF : IsModulusCovariant F)

include hFs hF in
/-- Levi equivariance: `F^♮(ι(A) y) = |det A| F^♮(y)`. -/
theorem natural_iota_mul (A : Langlands.GeneralLinear m ℝ) (y : Langlands.GeneralLinear (m + 1) ℝ) :
    natural F (iotaGL A * y) =
      ((|(A : Matrix (Fin m) (Fin m) ℝ).det| : ℝ) : ℂ) * natural F y := by
  have hinv := KIntegralInvariance.integral_mul_eq (contMDiff_leviSlice hFs y)
    (isModulusEquivariant_of_covariant (leviSlice_covariant hF y)) A
  have hA : ((|(A : Matrix (Fin m) (Fin m) ℝ).det| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)).ne_zero
  have h1 : ∀ k : unitaryCompact ℝ m, leviSlice F y ((k : Langlands.GeneralLinear m ℝ) * A) =
      F (iotaGL (k : Langlands.GeneralLinear m ℝ) * (iotaGL A * y)) *
        ((|(A : Matrix (Fin m) (Fin m) ℝ).det| : ℝ) : ℂ)⁻¹ := by
    intro k
    unfold leviSlice
    rw [map_mul, mul_assoc, Units.val_mul, Matrix.det_mul, abs_mul, abs_det_unitary, one_mul]
  have h2 : ∀ k : unitaryCompact ℝ m, leviSlice F y (k : Langlands.GeneralLinear m ℝ) =
      F (iotaGL (k : Langlands.GeneralLinear m ℝ) * y) := by
    intro k
    unfold leviSlice
    rw [abs_det_unitary]
    simp
  rw [integral_congr_ae (ae_of_all _ h1), integral_congr_ae (ae_of_all _ h2),
    integral_mul_const] at hinv
  unfold natural
  rw [← hinv]
  field_simp

/-- `d(a)` as an element of `GL_{m+1}(ℝ)`. -/
def dlastGL (a : ℝˣ) : Langlands.GeneralLinear (m + 1) ℝ :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits fun i => Fin.lastCases a (fun _ => 1) i

theorem dlastGL_val (a : ℝˣ) :
    ((dlastGL (m := m) a : Langlands.GeneralLinear (m + 1) ℝ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = dlast (a : ℝ) := by
  rw [dlastGL, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, dlast]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp

theorem modulusCharacter_dlast (a : ℝˣ) :
    modulusCharacter (m + 1) (fun i => Fin.lastCases a (fun _ => 1) i) =
      ((|(a : ℝ)| : ℝ) : ℂ) ^ (-(m : ℂ)) := by
  rw [modulusCharacter, Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Units.val_one, abs_one,
    Complex.ofReal_one, Complex.one_cpow, Finset.prod_const_one, one_mul, Fin.val_last]
  congr 1
  push_cast
  ring

include hF in
theorem natural_dlast_mul (a : ℝˣ) (x : Langlands.GeneralLinear (m + 1) ℝ) :
    natural F (dlastGL a * x) = ((|(a : ℝ)| : ℝ) : ℂ) ^ (-(m : ℂ)) * natural F x := by
  unfold natural
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  have hcomm : iotaGL (k : Langlands.GeneralLinear m ℝ) * dlastGL a =
      dlastGL a * iotaGL (k : Langlands.GeneralLinear m ℝ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, iotaGL_val, dlastGL_val, iota_mul_dlast]
  have := hF (fun i => Fin.lastCases a (fun _ => 1) i) 1
    (iotaGL (k : Langlands.GeneralLinear m ℝ) * x)
  rw [OneMemClass.coe_one, mul_one, modulusCharacter_dlast] at this
  show F (iotaGL (k : Langlands.GeneralLinear m ℝ) * (dlastGL a * x)) = _
  rw [← mul_assoc, hcomm, mul_assoc]
  exact this

/-- `n(c)` as an element of the upper unipotent group. -/
def nPU (c : Fin m → ℝ) : Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ :=
  ⟨⟨nP c, nP (-c), by
      ext i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
        simp [nP, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply,
          Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm],
    by
      ext i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
        simp [nP, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply,
          Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]⟩,
    nP_isUpperTriangular c, nP_diag c⟩

include hF in
theorem natural_nP_mul (c : Fin m → ℝ) (x : Langlands.GeneralLinear (m + 1) ℝ) :
    natural F ((nPU c : Langlands.GeneralLinear (m + 1) ℝ) * x) = natural F x := by
  unfold natural
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  have hcomm : iotaGL (k : Langlands.GeneralLinear m ℝ) * (nPU c : Langlands.GeneralLinear (m + 1) ℝ) =
      (nPU (((k : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) *ᵥ c) :
        Langlands.GeneralLinear (m + 1) ℝ) * iotaGL (k : Langlands.GeneralLinear m ℝ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, iotaGL_val]
    exact iota_mul_nP _ c
  simp only
  rw [← mul_assoc, hcomm, mul_assoc]
  exact covariant_upperUnipotent hF _ _

include hFs hF in
/-- **`P_{m,1}`-equivariance of `F^♮`.** If the last row of `p` is `(0, …, 0, a)`, then
`F^♮(p x) = |det p| |a|^{-(m+1)} F^♮(x)`. -/
theorem natural_mul_lastRow (p : Langlands.GeneralLinear (m + 1) ℝ)
    (hp : ∀ j : Fin m, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j.castSucc = 0)
    (x : Langlands.GeneralLinear (m + 1) ℝ) :
    natural F (p * x) =
      ((|(p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| : ℝ) : ℂ) *
        ((|(p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) (Fin.last m)| : ℝ) : ℂ) ^
          (-((m : ℂ) + 1)) * natural F x := by
  set P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    with hPdef
  set a := P (Fin.last m) (Fin.last m) with hadef
  have hPdet : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp (Units.isUnit p)).ne_zero
  have ha : a ≠ 0 := by
    intro h
    apply hPdet
    refine Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) fun j => ?_
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · exact h
    · exact hp j'
  have hdetP := det_eq_mul_det_topLeft hp ha
  have hA : (topLeft P).det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdetP
    exact hPdet hdetP
  set AGL : Langlands.GeneralLinear m ℝ :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA)).unit with hAGL
  set aU : ℝˣ := Units.mk0 a ha with haU
  set c : Fin m → ℝ := fun i => P i.castSucc (Fin.last m) / a with hc
  have hdec : p = (nPU c : Langlands.GeneralLinear (m + 1) ℝ) * iotaGL AGL * dlastGL aU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, iotaGL_val, dlastGL_val]
    exact eq_nP_mul_iota_mul_dlast hp ha
  have hAval : (AGL : Matrix (Fin m) (Fin m) ℝ) = topLeft P := IsUnit.unit_spec _
  rw [hdec, mul_assoc, mul_assoc, natural_nP_mul hF, natural_iota_mul hFs hF,
    natural_dlast_mul hF, hAval]
  have haC : ((|a| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr ha
  have hpow : ((|a| : ℝ) : ℂ) ^ (-((m : ℂ) + 1)) =
      ((|a| : ℝ) : ℂ) ^ (-(m : ℂ)) * ((|a| : ℝ) : ℂ)⁻¹ := by
    rw [neg_add, Complex.cpow_add _ _ haC, Complex.cpow_neg_one]
  change _ = ((|P.det| : ℝ) : ℂ) * ((|a| : ℝ) : ℂ) ^ (-((m : ℂ) + 1)) * _
  rw [hpow, hdetP, abs_mul, Complex.ofReal_mul]
  field_simp
  rw [show ((aU : ℝˣ) : ℝ) = a from rfl, ← hadef]
  ring

/-! ### The chart matrices `J(r)` -/

/-- `J(r)`: the identity matrix with last row replaced by `r`. -/
def Jmat (r : Fin (m + 1) → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (r j)
    (fun i' => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i'.castSucc j) i

theorem Jmat_isLowerTriangular (r : Fin (m + 1) → ℝ) : (Jmat r).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  have hi : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
  obtain ⟨i', rfl⟩ : ∃ i', i = i'.castSucc := ⟨i.castPred hi, by simp⟩
  simp only [Jmat, Matrix.of_apply, Fin.lastCases_castSucc]
  exact Matrix.one_apply_ne (ne_of_lt hij)

theorem det_Jmat (r : Fin (m + 1) → ℝ) : (Jmat r).det = r (Fin.last m) := by
  rw [Matrix.det_of_isLowerTriangular _ (Jmat_isLowerTriangular r), Fin.prod_univ_castSucc]
  simp [Jmat]

/-- `J(r)` as an element of `GL_{m+1}(ℝ)` when `r_m ≠ 0`. -/
def JGL (r : Fin (m + 1) → ℝ) (hr : r (Fin.last m) ≠ 0) : Langlands.GeneralLinear (m + 1) ℝ :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Jmat]; exact isUnit_iff_ne_zero.mpr hr)).unit

theorem JGL_val (r : Fin (m + 1) → ℝ) (hr : r (Fin.last m) ≠ 0) :
    ((JGL r hr : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      Jmat r := IsUnit.unit_spec _

theorem Jmat_smul (s : ℝ) (r : Fin (m + 1) → ℝ) : Jmat (s • r) = dlast s * Jmat r := by
  ext i j
  rw [dlast, Matrix.diagonal_mul]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp [Jmat]

include hF in
/-- `F^♮(J(s r)) = |s|^{-m} F^♮(J(r))`. -/
theorem natural_Jmat_smul {s : ℝ} (hs : s ≠ 0) (r : Fin (m + 1) → ℝ) (hr : r (Fin.last m) ≠ 0)
    (hsr : (s • r) (Fin.last m) ≠ 0) :
    natural F (JGL (s • r) hsr) = ((|s| : ℝ) : ℂ) ^ (-(m : ℂ)) * natural F (JGL r hr) := by
  have h : JGL (s • r) hsr = dlastGL (Units.mk0 s hs) * JGL r hr := by
    apply Units.ext
    rw [Units.val_mul, JGL_val, JGL_val, dlastGL_val, Units.val_mk0, Jmat_smul]
  rw [h, natural_dlast_mul hF, Units.val_mk0]

include hFs hF in
/-- For `κ ∈ O(m+1)` with last row `r`, `r_m ≠ 0`: `F^♮(J(r)) = |r_m| F^♮(κ)`. -/
theorem natural_Jmat_lastRow (κ : unitaryCompact ℝ (m + 1))
    (hr : OrthogonalLastRowIntegral.lastRow κ (Fin.last m) ≠ 0) :
    natural F (JGL (OrthogonalLastRowIntegral.lastRow κ) hr) =
      ((|OrthogonalLastRowIntegral.lastRow κ (Fin.last m)| : ℝ) : ℂ) *
        natural F (κ : Langlands.GeneralLinear (m + 1) ℝ) := by
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((κ : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) with hK
  have hKK : K * Kᵀ = 1 := OrthogonalLastRowIntegral.mul_transpose_eq_one κ
  set p : Langlands.GeneralLinear (m + 1) ℝ :=
    JGL (OrthogonalLastRowIntegral.lastRow κ) hr * (κ : Langlands.GeneralLinear (m + 1) ℝ)⁻¹
    with hpdef
  have hinvK : (((κ : Langlands.GeneralLinear (m + 1) ℝ)⁻¹ : Langlands.GeneralLinear (m + 1) ℝ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = Kᵀ := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hKK]
  have hlast : ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j := by
    intro j
    rw [hpdef, Units.val_mul, JGL_val, hinvK, ← hKK]
    simp [Jmat, Matrix.mul_apply, OrthogonalLastRowIntegral.lastRow, hK]
  have hp : ∀ j : Fin m, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j.castSucc = 0 :=
    fun j => by rw [hlast, Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm]
  have hpl : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) (Fin.last m) = 1 := by
    rw [hlast, Matrix.one_apply_eq]
  have hdet : |(p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| =
      |OrthogonalLastRowIntegral.lastRow κ (Fin.last m)| := by
    rw [hpdef, Units.val_mul, JGL_val, Matrix.det_mul, det_Jmat, abs_mul, hinvK,
      Matrix.det_transpose, abs_det_unitary, mul_one]
  have hJ : JGL (OrthogonalLastRowIntegral.lastRow κ) hr = p * (κ : Langlands.GeneralLinear (m + 1) ℝ) := by
    rw [hpdef, inv_mul_cancel_right]
  rw [hJ, natural_mul_lastRow hFs hF p hp, hpl, hdet]
  simp

/-! ### The homogeneous function of the last row -/

/-- The matrix-level average `Ñ(Y) = ∫_{O(m)} F̃(ι(k) Y) dk`, `F̃` the extension by zero. -/
def naturalMat (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ)
    (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : ℂ :=
  ∫ k : unitaryCompact ℝ m, unitsExtension F
    (iota ((k : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) * Y) ∂haarK m

omit hFs in
theorem naturalMat_val (x : Langlands.GeneralLinear (m + 1) ℝ) :
    naturalMat F (x : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = natural F x := by
  unfold naturalMat natural
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only
  rw [← iotaGL_val, ← Units.val_mul, unitsExtension_val]

/-- `Φ(r) = F^♮(J(r)) |r_m|⁻¹ |r|^{m+1}` (and `0` if `r_m = 0`). -/
def phiF (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ) (r : Fin (m + 1) → ℝ) : ℂ :=
  if r (Fin.last m) = 0 then 0 else
    naturalMat F (Jmat r) * ((|r (Fin.last m)| : ℝ) : ℂ)⁻¹ *
      ((Real.sqrt (OrthogonalLastRowIntegral.sqNorm r) ^ (m + 1) : ℝ) : ℂ)

omit hFs hF in
theorem phiF_eq (r : Fin (m + 1) → ℝ) (hr : r (Fin.last m) ≠ 0) :
    phiF F r = natural F (JGL r hr) * ((|r (Fin.last m)| : ℝ) : ℂ)⁻¹ *
      ((Real.sqrt (OrthogonalLastRowIntegral.sqNorm r) ^ (m + 1) : ℝ) : ℂ) := by
  rw [phiF, ite_eq_right hr, ← JGL_val r hr, naturalMat_val]

include hF in
theorem phiF_homogeneous : OrthogonalLastRowIntegral.IsHomogeneousZero (phiF F) := by
  intro s hs r
  by_cases hr : r (Fin.last m) = 0
  · have hsr : (s • r) (Fin.last m) = 0 := by simp [hr]
    rw [phiF, ite_eq_left hsr, phiF, ite_eq_left hr]
  · have hsr : (s • r) (Fin.last m) ≠ 0 := by simp [hs, hr]
    rw [phiF_eq _ hsr, phiF_eq _ hr, natural_Jmat_smul hF hs r hr hsr,
      OrthogonalLastRowIntegral.sqNorm_smul, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    have hsC : ((|s| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hs
    have hrC : ((|r (Fin.last m)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hr
    rw [Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    field_simp
    ring

theorem sqNorm_lastRow (κ : unitaryCompact ℝ (m + 1)) :
    OrthogonalLastRowIntegral.sqNorm (OrthogonalLastRowIntegral.lastRow κ) = 1 := by
  have h := congrFun (congrFun (OrthogonalLastRowIntegral.mul_transpose_eq_one κ) (Fin.last m))
    (Fin.last m)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h, OrthogonalLastRowIntegral.sqNorm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [OrthogonalLastRowIntegral.lastRow, sq]

include hFs hF in
theorem phiF_lastRow (κ : unitaryCompact ℝ (m + 1))
    (hr : OrthogonalLastRowIntegral.lastRow κ (Fin.last m) ≠ 0) :
    phiF F (OrthogonalLastRowIntegral.lastRow κ) = natural F (κ : Langlands.GeneralLinear (m + 1) ℝ) := by
  rw [phiF_eq _ hr, natural_Jmat_lastRow hFs hF κ hr, sqNorm_lastRow, Real.sqrt_one, one_pow]
  have hrC : ((|OrthogonalLastRowIntegral.lastRow κ (Fin.last m)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr hr
  push_cast
  field_simp

include hFs hF in
theorem exists_bound_phiF : ∃ C, ∀ r, ‖phiF F r‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hFs.continuous.comp continuous_subtype_val :
      Continuous fun κ : unitaryCompact ℝ (m + 1) => F κ).continuousOn)
  have hnat : ∀ κ : unitaryCompact ℝ (m + 1),
      ‖natural F (κ : Langlands.GeneralLinear (m + 1) ℝ)‖ ≤ C := by
    intro κ
    have h := norm_integral_le_of_norm_le_const (μ := haarK m) (C := C)
      (f := fun k : unitaryCompact ℝ m =>
        F (iotaGL (k : Langlands.GeneralLinear m ℝ) * (κ : Langlands.GeneralLinear (m + 1) ℝ)))
      (ae_of_all _ fun k => hC ⟨_, mul_mem (iotaGL_mem_unitaryCompact k.2) κ.2⟩ trivial)
    rw [probReal_univ, mul_one] at h
    exact h
  refine ⟨max C 0, fun r => ?_⟩
  by_cases hr : r (Fin.last m) = 0
  · rw [phiF, ite_eq_left hr, norm_zero]
    exact le_max_right _ _
  · have hq : 0 < OrthogonalLastRowIntegral.sqNorm r := by
      have : 0 < r (Fin.last m) ^ 2 := by positivity
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => r j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ _))
    set t := Real.sqrt (OrthogonalLastRowIntegral.sqNorm r) with ht
    have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    set u := t⁻¹ • r with hu
    have hu1 : OrthogonalLastRowIntegral.sqNorm u = 1 := by
      rw [hu, OrthogonalLastRowIntegral.sqNorm_smul, inv_pow, ht, Real.sq_sqrt hq.le,
        inv_mul_cancel₀ hq.ne']
    obtain ⟨K₀, hK₀, hlast⟩ := OrthogonalLastRowIntegral.exists_orthogonal_lastRow u hu1
    have hK₀mem : K₀ ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hK₀
    let κ₀ : unitaryCompact ℝ (m + 1) := ⟨Unitary.toUnits ⟨K₀, hK₀mem⟩, hK₀mem⟩
    have hrow : OrthogonalLastRowIntegral.lastRow κ₀ = u := hlast
    have hul : OrthogonalLastRowIntegral.lastRow κ₀ (Fin.last m) ≠ 0 := by
      rw [hrow, hu, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero ht0) hr
    have hrt : r = t • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ ht0, one_smul]
    rw [hrt, phiF_homogeneous hF t ht0, ← hrow, phiF_lastRow hFs hF κ₀ hul]
    exact le_trans (hnat κ₀) (le_max_left _ _)

omit hF in
include hFs in
theorem measurable_unitsExtension : Measurable (unitsExtension F) := by
  classical
  have h : unitsExtension F = {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ | IsUnit Y}.piecewise
      (unitsExtension F) (fun _ => 0) := by
    funext Y
    by_cases hY : IsUnit Y
    · simp [Set.piecewise, hY]
    · simp [Set.piecewise, hY, unitsExtension]
  rw [h]
  exact ContinuousOn.measurable_piecewise (contDiffOn_unitsExtension hFs).continuousOn
    continuousOn_const isOpen_setOf_isUnit_matrix.measurableSet

omit hFs hF in
theorem measurable_iota_mul_Jmat :
    Measurable fun p : (Fin (m + 1) → ℝ) × unitaryCompact ℝ m =>
      iota ((p.2 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) * Jmat p.1 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have hform : (fun p : (Fin (m + 1) → ℝ) × unitaryCompact ℝ m =>
      (iota ((p.2 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) * Jmat p.1) i j) =
      fun p => ∑ l, iota ((p.2 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i l *
        Jmat p.1 l j := funext fun p => rfl
  rw [hform]
  refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
  · have hc : Continuous fun k : unitaryCompact ℝ m =>
        iota ((k : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i l :=
      (continuous_apply l).comp ((continuous_apply i).comp
        (contDiff_iota.continuous.comp RealPrincipalSeriesDuality.continuous_unitaryCompact_val))
    exact hc.measurable.comp measurable_snd
  · induction l using Fin.lastCases with
    | last =>
      have : (fun p : (Fin (m + 1) → ℝ) × unitaryCompact ℝ m => Jmat p.1 (Fin.last m) j) =
          fun p => p.1 j := funext fun p => by simp [Jmat]
      rw [this]
      exact (measurable_pi_apply j).comp measurable_fst
    | cast l' =>
      have : (fun p : (Fin (m + 1) → ℝ) × unitaryCompact ℝ m => Jmat p.1 l'.castSucc j) =
          fun _ => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) l'.castSucc j :=
        funext fun p => by simp [Jmat]
      rw [this]
      exact measurable_const

omit hF in
include hFs in
theorem measurable_phiF : Measurable (phiF F) := by
  unfold phiF
  refine Measurable.ite (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
    measurable_const ?_
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · have hj : Measurable fun p : (Fin (m + 1) → ℝ) × unitaryCompact ℝ m => unitsExtension F
        (iota ((p.2 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) * Jmat p.1) :=
      (measurable_unitsExtension hFs).comp measurable_iota_mul_Jmat
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := haarK m)).measurable
  · exact (Complex.continuous_ofReal.comp (continuous_abs.comp
      (continuous_apply (Fin.last m)))).measurable.inv
  · have hc : Continuous fun r : Fin (m + 1) → ℝ =>
        ((Real.sqrt (OrthogonalLastRowIntegral.sqNorm r) ^ (m + 1) : ℝ) : ℂ) := by
      unfold OrthogonalLastRowIntegral.sqNorm
      fun_prop
    exact hc.measurable

omit hFs hF in
/-- The last diagonal entry of a Haar-random orthogonal matrix is almost surely nonzero. -/
theorem ae_lastRow_last_ne_zero :
    ∀ᵐ κ ∂haarK (m + 1), OrthogonalLastRowIntegral.lastRow κ (Fin.last m) ≠ 0 := by
  classical
  set Φ₀ : (Fin (m + 1) → ℝ) → ℂ := fun x => if x (Fin.last m) = 0 then 1 else 0 with hΦ₀
  have hmeas : Measurable Φ₀ :=
    Measurable.ite (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
      measurable_const measurable_const
  have hbound : ∀ x, ‖Φ₀ x‖ ≤ 1 := fun x => by
    by_cases h : x (Fin.last m) = 0 <;> simp [hΦ₀, h]
  have hhom : OrthogonalLastRowIntegral.IsHomogeneousZero Φ₀ := by
    intro s hs x
    simp [hΦ₀, hs]
  have h := OrthogonalLastRowIntegral.integral_lastRow hmeas hbound hhom
  have hzero : ∀ v : Fin m → ℝ, Φ₀ (Fin.snoc v 1) * (OrthogonalLastRowIntegral.chartWeight v : ℂ) = 0 :=
    fun v => by simp [hΦ₀]
  simp only [hzero, integral_zero, mul_zero] at h
  -- `h : ∫ Φ₀ (lastRow κ) = 0`; pass to the real indicator
  set g : unitaryCompact ℝ (m + 1) → ℝ := fun κ =>
    if OrthogonalLastRowIntegral.lastRow κ (Fin.last m) = 0 then 1 else 0 with hg
  have hgC : (fun κ => Φ₀ (OrthogonalLastRowIntegral.lastRow κ)) = fun κ => ((g κ : ℝ) : ℂ) := by
    funext κ
    by_cases hκ : OrthogonalLastRowIntegral.lastRow κ (Fin.last m) = 0 <;> simp [hΦ₀, hg, hκ]
  rw [hgC, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hgc : Continuous fun κ : unitaryCompact ℝ (m + 1) =>
      OrthogonalLastRowIntegral.lastRow κ (Fin.last m) :=
    (continuous_apply (Fin.last m)).comp ((continuous_apply (Fin.last m)).comp
      RealPrincipalSeriesDuality.continuous_unitaryCompact_val)
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_eq_fun hgc.measurable measurable_const) measurable_const
      measurable_const
  have hgi : Integrable g (haarK (m + 1)) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun κ => by
      by_cases hκ : OrthogonalLastRowIntegral.lastRow κ (Fin.last m) = 0 <;> simp [hg, hκ])
  have hae := (integral_eq_zero_iff_of_nonneg (fun κ => by
    by_cases hκ : OrthogonalLastRowIntegral.lastRow κ (Fin.last m) = 0 <;> simp [hg, hκ]) hgi).mp h
  filter_upwards [hae] with κ hκ
  intro h0
  simp [hg, h0] at hκ

omit hF in
include hFs in
/-- `∫_{O(m+1)} F = ∫_{O(m+1)} F^♮`. -/
theorem integral_eq_integral_natural :
    ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) =
      ∫ κ, natural F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hFs.continuous.comp continuous_subtype_val :
      Continuous fun κ : unitaryCompact ℝ (m + 1) => F κ).continuousOn)
  set G : unitaryCompact ℝ m × unitaryCompact ℝ (m + 1) → ℂ := fun p =>
    F (iotaGL (p.1 : Langlands.GeneralLinear m ℝ) * (p.2 : Langlands.GeneralLinear (m + 1) ℝ))
    with hGdef
  have hGm : Measurable G := by
    have hform : G = fun p => unitsExtension F
        (iota ((p.1 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) *
          ((p.2 : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) := by
      funext p
      rw [hGdef]
      simp only
      rw [← iotaGL_val, ← Units.val_mul, unitsExtension_val]
    rw [hform]
    refine (measurable_unitsExtension hFs).comp ?_
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    have hform2 : (fun p : unitaryCompact ℝ m × unitaryCompact ℝ (m + 1) =>
        (iota ((p.1 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) *
          ((p.2 : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) i j) =
        fun p => ∑ l, iota ((p.1 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i l *
          ((p.2 : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) l j :=
      funext fun p => rfl
    rw [hform2]
    refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
    · exact ((continuous_apply l).comp ((continuous_apply i).comp
        (contDiff_iota.continuous.comp
          RealPrincipalSeriesDuality.continuous_unitaryCompact_val))).measurable.comp measurable_fst
    · exact ((continuous_apply j).comp ((continuous_apply l).comp
        RealPrincipalSeriesDuality.continuous_unitaryCompact_val)).measurable.comp measurable_snd
  have hGi : Integrable G ((haarK m).prod (haarK (m + 1))) :=
    Integrable.of_bound hGm.aestronglyMeasurable C (ae_of_all _ fun p =>
      hC ⟨_, mul_mem (iotaGL_mem_unitaryCompact p.1.2) p.2.2⟩ trivial)
  have hleft : ∀ k : unitaryCompact ℝ m,
      ∫ κ, G (k, κ) ∂haarK (m + 1) = ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) :=
    fun k => integral_mul_left_eq_self (μ := haarK (m + 1))
      (fun κ : unitaryCompact ℝ (m + 1) => F (κ : Langlands.GeneralLinear (m + 1) ℝ)) (iotaK k)
  calc ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1)
      = ∫ k : unitaryCompact ℝ m, (∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1))
          ∂haarK m := by
        rw [integral_const, probReal_univ, one_smul]
    _ = ∫ k : unitaryCompact ℝ m, (∫ κ, G (k, κ) ∂haarK (m + 1)) ∂haarK m :=
        integral_congr_ae (ae_of_all _ fun k => (hleft k).symm)
    _ = ∫ κ, ∫ k, G (k, κ) ∂haarK m ∂haarK (m + 1) :=
        integral_integral_swap (f := fun k κ => G (k, κ)) hGi
    _ = ∫ κ, natural F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) := rfl

omit hFs hF in
theorem snoc_last_ne_zero (v : Fin m → ℝ) : (Fin.snoc v 1 : Fin (m + 1) → ℝ) (Fin.last m) ≠ 0 := by
  simp

/-- The chart point `J(v, 1)`: the identity matrix with last row replaced by `(v, 1)`. -/
def chartGL (v : Fin m → ℝ) : Langlands.GeneralLinear (m + 1) ℝ :=
  JGL (Fin.snoc v 1) (snoc_last_ne_zero v)

omit hFs hF in
theorem phiF_snoc (v : Fin m → ℝ) :
    phiF F (Fin.snoc v 1) * (OrthogonalLastRowIntegral.chartWeight v : ℂ) =
      natural F (chartGL v) := by
  rw [phiF_eq _ (snoc_last_ne_zero v), OrthogonalLastRowIntegral.sqNorm_snoc, Fin.snoc_last,
    OrthogonalLastRowIntegral.chartWeight, chartGL]
  have hq : 0 < 1 + OrthogonalLastRowIntegral.sqNorm v := by
    unfold OrthogonalLastRowIntegral.sqNorm
    positivity
  have hpos : (Real.sqrt (1 + OrthogonalLastRowIntegral.sqNorm v) ^ (m + 1) : ℝ) ≠ 0 :=
    (pow_pos (Real.sqrt_pos.mpr hq) _).ne'
  have hpos' : ((Real.sqrt (1 + OrthogonalLastRowIntegral.sqNorm v) ^ (m + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos
  rw [one_pow, add_comm (OrthogonalLastRowIntegral.sqNorm v) 1, abs_one, Complex.ofReal_one,
    inv_one, mul_one, Complex.ofReal_inv, mul_assoc, mul_inv_cancel₀ hpos', mul_one]

/-- The normalizing constant `c_m = (∫_ℝ |t|^m e^{-t²} dt) / (∫_{ℝ^{m+1}} e^{-|x|²} dx)`. -/
def chartConstant (m : ℕ) : ℝ :=
  OrthogonalLastRowIntegral.gaussianMoment m /
    ∫ x : Fin (m + 1) → ℝ, OrthogonalLastRowIntegral.gaussian x

theorem gaussianMoment_pos (m : ℕ) : 0 < OrthogonalLastRowIntegral.gaussianMoment m := by
  unfold OrthogonalLastRowIntegral.gaussianMoment
  have hint : Integrable (fun t : ℝ => |t| ^ m * Real.exp (-t ^ 2)) := by
    have := OrthogonalLastRowIntegral.integrable_abs_pow_mul_exp m (a := 1) one_pos
    simpa using this
  rw [integral_pos_iff_support_of_nonneg (fun t => by positivity) hint]
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (fun t : ℝ => |t| ^ m * Real.exp (-t ^ 2)) := by
    intro t ht
    simp only [Function.mem_support]
    exact (mul_pos (pow_pos (abs_pos.mpr (ne_of_gt ht)) m) (Real.exp_pos _)).ne'
  exact lt_of_lt_of_le (by simp) (measure_mono hsub)

theorem chartConstant_pos (m : ℕ) : 0 < chartConstant m :=
  div_pos (gaussianMoment_pos m) OrthogonalLastRowIntegral.integral_gaussian_pos

include hFs hF in
/-- **Maximal-parabolic integration formula.**
`∫_{O(m+1)} F = c_m ∫_{ℝ^m} ∫_{O(m)} F(ι(k) J(v, 1)) dk dv`. -/
theorem integral_eq_chart :
    ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) =
      (chartConstant m : ℂ) * ∫ v : Fin m → ℝ, natural F (chartGL v) := by
  rw [integral_eq_integral_natural hFs]
  have hae : (fun κ : unitaryCompact ℝ (m + 1) => natural F (κ : Langlands.GeneralLinear (m + 1) ℝ))
      =ᵐ[haarK (m + 1)] fun κ => phiF F (OrthogonalLastRowIntegral.lastRow κ) := by
    filter_upwards [ae_lastRow_last_ne_zero] with κ hκ
    exact (phiF_lastRow hFs hF κ hκ).symm
  rw [integral_congr_ae hae]
  obtain ⟨C, hC⟩ := exists_bound_phiF hFs hF
  rw [OrthogonalLastRowIntegral.integral_lastRow (measurable_phiF hFs) hC (phiF_homogeneous hF),
    chartConstant]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun v => phiF_snoc v)

end Natural

end MaximalParabolicIntegration

open MaximalParabolicIntegration RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

/-- **Statement (the `O(m+1)`-integral in coordinates of the maximal parabolic `P_{m,1}`).**
Let `F` be a smooth complex function on `GL_{m+1}(ℝ)` such that
`F(diag(a) u g) = ∏ᵢ |aᵢ|^{m - 2i} F(g)` for every `a ∈ (ℝˣ)^{m+1}`, every upper unipotent `u` and
every `g` (`IsModulusCovariant`, i.e. `F` lies in the principal series of the modulus character
`δ_B`). Then, with normalized Haar measures `haarK`,
`∫_{O(m+1)} F(κ) dκ = c_m ∫_{ℝ^m} ∫_{O(m)} F(ι(k) J(v, 1)) dk dv`,
where `ι(k) = diag(k, 1)`, `J(v, 1)` is the identity matrix with last row `(v, 1)` (so
`ι(k) J(v, 1)` is the block matrix with rows `(k, 0)` and `(v, 1)`), and
`c_m = (∫_ℝ |t|^m e^{-t²} dt) / (∫_{ℝ^{m+1}} e^{-∑ xᵢ²} dx) > 0`. -/
def MaximalParabolicIntegrationStatement : Prop :=
  ∀ (m : ℕ) (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ),
    ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ F → IsModulusCovariant F →
      ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) =
        (((∫ t : ℝ, |t| ^ m * Real.exp (-t ^ 2)) /
            ∫ x : Fin (m + 1) → ℝ, Real.exp (-∑ i, x i ^ 2) : ℝ) : ℂ) *
          ∫ v : Fin m → ℝ, ∫ k : unitaryCompact ℝ m,
            F (iotaGL (k : Langlands.GeneralLinear m ℝ) * chartGL v) ∂haarK m

theorem maximalParabolicIntegration : MaximalParabolicIntegrationStatement :=
  fun _ _ hFs hF => integral_eq_chart hFs hF

end Langlands.Archimedean
