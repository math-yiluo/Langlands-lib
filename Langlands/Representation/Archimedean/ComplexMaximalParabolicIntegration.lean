import Langlands.Representation.Archimedean.ComplexKIntegralInvariance
import Langlands.Representation.Archimedean.ComplexLastRowIntegral

/-!
# The `U(n)`-integral in coordinates of the maximal parabolic subgroup `P_{n-1,1}` of `GL_n(ℂ)`

For `F` in the smooth principal series of `GL_{m+1}(ℂ)` of the modulus character of the upper
triangular Borel subgroup,
`∫_{U(m+1)} F = c_m ∫_{ℂ^m} ∫_{U(m)} F(diag(k, 1) J(v, 1)) dk dv`
(`ComplexMaximalParabolicIntegration.integral_eq_chart`), where `J(v, 1)` is the identity matrix
with last row `(v, 1)`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexMaximalParabolicIntegration

open ComplexDuality ComplexKIntegralInvariance

variable {m : ℕ}

/-! ## Block matrices for `P_{m,1}` -/

/-- `ι(A) = diag(A, 1)`. -/
def iota (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

@[simp] theorem iota_last_last (A : Matrix (Fin m) (Fin m) ℂ) :
    iota A (Fin.last m) (Fin.last m) = 1 := by simp [iota]

@[simp] theorem iota_last_castSucc (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    iota A (Fin.last m) j.castSucc = 0 := by simp [iota]

@[simp] theorem iota_castSucc_last (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    iota A i.castSucc (Fin.last m) = 0 := by simp [iota]

@[simp] theorem iota_castSucc_castSucc (A : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    iota A i.castSucc j.castSucc = A i j := by simp [iota]

theorem iota_mul (A B : Matrix (Fin m) (Fin m) ℂ) : iota (A * B) = iota A * iota B := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem iota_one : iota (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem iota_conjTranspose (A : Matrix (Fin m) (Fin m) ℂ) : (iota A)ᴴ = iota Aᴴ := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

theorem det_iota (A : Matrix (Fin m) (Fin m) ℂ) : (iota A).det = A.det := by
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
def dlast (a : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.diagonal fun i => Fin.lastCases a (fun _ => 1) i

theorem iota_mul_dlast (A : Matrix (Fin m) (Fin m) ℂ) (a : ℂ) :
    iota A * dlast a = dlast a * iota A := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [dlast, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- `n(c)`: the identity with the column `c` above the last diagonal entry. -/
def nP (c : Fin m → ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (c i') (fun j' => if i' = j' then 1 else 0) j) i

theorem iota_mul_nP (A : Matrix (Fin m) (Fin m) ℂ) (c : Fin m → ℂ) :
    iota A * nP c = nP (A *ᵥ c) * iota A := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [nP, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]

theorem nP_isUpperTriangular (c : Fin m → ℂ) : (nP c).IsUpperTriangular := by
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

theorem nP_diag (c : Fin m → ℂ) (i : Fin (m + 1)) : nP c i i = 1 := by
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp [nP]

theorem det_nP (c : Fin m → ℂ) : (nP c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (nP_isUpperTriangular c)]
  simp [nP_diag]

theorem det_dlast (a : ℂ) : (dlast (m := m) a).det = a := by
  rw [dlast, Matrix.det_diagonal, Fin.prod_univ_castSucc]
  simp

/-- The top-left block. -/
def topLeft (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => p i.castSucc j.castSucc

/-- **Decomposition in `P_{m,1}`.** A matrix with last row `(0, …, 0, a)`, `a ≠ 0`, is
`n(c) · ι(A) · d(a)`. -/
theorem eq_nP_mul_iota_mul_dlast {p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
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

theorem det_eq_mul_det_topLeft {p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hp : ∀ j : Fin m, p (Fin.last m) j.castSucc = 0) (ha : p (Fin.last m) (Fin.last m) ≠ 0) :
    p.det = p (Fin.last m) (Fin.last m) * (topLeft p).det := by
  conv_lhs => rw [eq_nP_mul_iota_mul_dlast hp ha]
  rw [Matrix.det_mul, Matrix.det_mul, det_nP, det_iota, det_dlast]
  ring

/-! ## The modulus character -/

/-- `|z|² ∈ ℂ`. -/
def normSqC (z : ℂ) : ℂ := ((‖z‖ ^ 2 : ℝ) : ℂ)

theorem normSqC_ne_zero {z : ℂ} (hz : z ≠ 0) : normSqC z ≠ 0 := by
  unfold normSqC
  exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)

theorem normSqC_mul (z w : ℂ) : normSqC (z * w) = normSqC z * normSqC w := by
  unfold normSqC
  rw [norm_mul, mul_pow]
  push_cast
  ring

theorem normSqC_one : normSqC 1 = 1 := by simp [normSqC]

theorem normSqC_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    normSqC (∏ i ∈ s, f i) = ∏ i ∈ s, normSqC (f i) := by
  unfold normSqC
  rw [norm_prod, ← Finset.prod_pow, Complex.ofReal_prod]

/-- The modulus character `diag(a) ↦ ∏ᵢ |aᵢ|^(2(n-1-2i))` of the upper triangular Borel subgroup. -/
def modulusValue (n : ℕ) (a : Fin n → ℂˣ) : ℂ :=
  ∏ i : Fin n, normSqC (a i : ℂ) ^ (((n : ℂ) - 1) - 2 * ((i : ℕ) : ℂ))

theorem principalSeriesCharacter_modulus (n : ℕ) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (modulusCharacter n) a = modulusValue n a := by
  rw [modulus_mul_eq, modulusValue]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha : normSqC (a i : ℂ) ≠ 0 := normSqC_ne_zero (a i).ne_zero
  unfold normSqC at ha ⊢
  rw [← Complex.cpow_add _ _ ha]
  congr 1
  ring

theorem modulusValue_one {n : ℕ} : modulusValue n (fun _ => 1) = 1 := by
  simp [modulusValue, normSqC]

/-- Left covariance of `F` under the Borel subgroup, from membership in the principal series of
the modulus character. -/
theorem covariant {n : ℕ} {F : Langlands.GeneralLinear n ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ n (modulusCharacter n)) (a : Fin n → ℂˣ)
    (u : Langlands.GeneralLinear.upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    F ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) * g) = modulusValue n a * F g := by
  rw [← principalSeriesCharacter_modulus]
  exact hF.2 a u g

theorem covariant_upperUnipotent {n : ℕ} {F : Langlands.GeneralLinear n ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ n (modulusCharacter n))
    (u : Langlands.GeneralLinear.upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) : F ((u : Langlands.GeneralLinear n ℂ) * g) = F g := by
  have := covariant hF (fun _ => 1) u g
  have h1 : (Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin n => (1 : ℂˣ)) :
      Langlands.GeneralLinear n ℂ) = 1 := map_one _
  rw [h1, one_mul, modulusValue_one, one_mul] at this
  exact this

/-! ## The Levi embedding on `GL` -/

/-- `ι` as a monoid homomorphism of matrices. -/
def iotaHom : Matrix (Fin m) (Fin m) ℂ →* Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ where
  toFun := iota
  map_one' := iota_one
  map_mul' := iota_mul

/-- `g ↦ diag(g, 1)` from `GL_m(ℂ)` to `GL_{m+1}(ℂ)`. -/
def iotaGL : Langlands.GeneralLinear m ℂ →* Langlands.GeneralLinear (m + 1) ℂ :=
  Units.map iotaHom

@[simp] theorem iotaGL_val (g : Langlands.GeneralLinear m ℂ) :
    ((iotaGL g : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      iota (g : Matrix (Fin m) (Fin m) ℂ) := rfl

theorem iotaGL_mem_unitaryCompact {k : Langlands.GeneralLinear m ℂ}
    (hk : k ∈ unitaryCompact ℂ m) : iotaGL k ∈ unitaryCompact ℂ (m + 1) := by
  change iota (k : Matrix (Fin m) (Fin m) ℂ) ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ
  have hk' := Matrix.mem_unitaryGroup_iff.mp hk
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, iota_conjTranspose,
    ← iota_mul]
  rw [Matrix.star_eq_conjTranspose] at hk'
  rw [hk', iota_one]

/-- `ι` on `U(m)`. -/
def iotaK (k : unitaryCompact ℂ m) : unitaryCompact ℂ (m + 1) :=
  ⟨iotaGL (k : Langlands.GeneralLinear m ℂ), iotaGL_mem_unitaryCompact k.2⟩

theorem iotaGL_mem_upperUnipotent (u : Langlands.GeneralLinear.upperUnipotent m ℂ) :
    iotaGL (u : Langlands.GeneralLinear m ℂ) ∈
      Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change j < i at hij
    change iota ((u : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) i j = 0
    have hj : j ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last i))
    obtain ⟨j', rfl⟩ : ∃ j', j = j'.castSucc := ⟨j.castPred hj, by simp⟩
    induction i using Fin.lastCases with
    | last => simp
    | cast i' =>
      rw [iota_castSucc_castSucc]
      exact u.2.1 (Fin.castSucc_lt_castSucc_iff.mp hij)
  · change iota ((u : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) i i = 1
    induction i using Fin.lastCases with
    | last => simp
    | cast i' =>
      rw [iota_castSucc_castSucc]
      exact u.2.2 i'

theorem iotaGL_diagonalUnits (a : Fin m → ℂˣ) :
    iotaGL (Langlands.GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℂ) =
      Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => Fin.lastCases 1 a i) := by
  apply Units.ext
  rw [iotaGL_val, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val,
    Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.diagonal_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem modulusValue_lastCases (a : Fin m → ℂˣ) :
    modulusValue (m + 1) (fun i => Fin.lastCases 1 a i) =
      modulusValue m a * ∏ i : Fin m, normSqC (a i : ℂ) := by
  rw [modulusValue, Fin.prod_univ_castSucc, modulusValue, ← Finset.prod_mul_distrib]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Units.val_one, normSqC_one,
    Complex.one_cpow, mul_one, Fin.val_castSucc]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha : normSqC (a i : ℂ) ≠ 0 := normSqC_ne_zero (a i).ne_zero
  have hexp : (((m + 1 : ℕ) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) =
      ((m : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) + 1 := by
    push_cast
    ring
  rw [hexp, Complex.cpow_add _ _ ha, Complex.cpow_one]

/-! ## The Levi slice -/

theorem det_upperUnipotent {n : ℕ} (u : Langlands.GeneralLinear.upperUnipotent n ℂ) :
    ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular u.2.1]
  exact Finset.prod_eq_one fun i _ => u.2.2 i

/-- The Levi slice `g ↦ F(ι(g) y) |det g|⁻²` on `GL_m(ℂ)`. -/
def leviSlice (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (y : Langlands.GeneralLinear (m + 1) ℂ)
    (g : Langlands.GeneralLinear m ℂ) : ℂ :=
  F (iotaGL g * y) * (normSqC (g : Matrix (Fin m) (Fin m) ℂ).det)⁻¹

theorem leviSlice_covariant {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1)))
    (y : Langlands.GeneralLinear (m + 1) ℂ) (a : Fin m → ℂˣ)
    (u : Langlands.GeneralLinear.upperUnipotent m ℂ) (g : Langlands.GeneralLinear m ℂ) :
    leviSlice F y ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a :
      Langlands.GeneralLinear m ℂ) * (u : Langlands.GeneralLinear m ℂ) * g) =
      modulusValue m a * leviSlice F y g := by
  have hu := iotaGL_mem_upperUnipotent u
  have h1 : iotaGL ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a :
      Langlands.GeneralLinear m ℂ) * (u : Langlands.GeneralLinear m ℂ) * g) * y =
      (Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => Fin.lastCases 1 a i) :
        Langlands.GeneralLinear (m + 1) ℂ) *
        ((⟨iotaGL (u : Langlands.GeneralLinear m ℂ), hu⟩ :
          Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ) :
            Langlands.GeneralLinear (m + 1) ℂ) * (iotaGL g * y) := by
    rw [map_mul, map_mul, iotaGL_diagonalUnits]
    simp only [mul_assoc]
  have hdet : ((((Langlands.GeneralLinear.Iwasawa.diagonalUnits a :
      Langlands.GeneralLinear m ℂ) * (u : Langlands.GeneralLinear m ℂ) * g :
        Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ).det) =
      (∏ i, (a i : ℂ)) * ((g : Matrix (Fin m) (Fin m) ℂ).det) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_upperUnipotent,
      Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.det_diagonal, mul_one]
  unfold leviSlice
  rw [h1, covariant hF, hdet, modulusValue_lastCases, normSqC_mul, normSqC_prod]
  have hne : (∏ i : Fin m, normSqC (a i : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => normSqC_ne_zero (a i).ne_zero
  rw [mul_inv]
  field_simp

/-- `ι` as an affine map of matrices: `ι(Y) = L(Y) + ι(0)`. -/
def iotaLin : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ where
  toFun Y := Matrix.of fun i j =>
    Fin.lastCases 0 (fun i' => Fin.lastCases 0 (fun j' => Y i' j') j) i
  map_add' Y Y' := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp
  map_smul' c Y := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp

theorem iota_eq_iotaLin_add (Y : Matrix (Fin m) (Fin m) ℂ) : iota Y = iotaLin Y + iota 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [iotaLin]

theorem contDiff_iota : ContDiff ℝ ∞ (iota (m := m)) := by
  have h : (iota (m := m)) = fun Y => (LinearMap.toContinuousLinearMap iotaLin) Y + iota 0 :=
    funext fun Y => by rw [iota_eq_iotaLin_add]; rfl
  rw [h]
  exact (LinearMap.toContinuousLinearMap iotaLin).contDiff.add contDiff_const

theorem contDiff_entry {n : ℕ} (p q : Fin n) :
    ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y p q) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun y => y p q, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem contDiff_det {n : ℕ} : ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y.det) := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry (σ i) i)

theorem leviSlice_mem {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1)))
    (y : Langlands.GeneralLinear (m + 1) ℂ) :
    leviSlice F y ∈ principalSeries ℂ m (modulusCharacter m) := by
  refine ⟨?_, fun a u g => ?_⟩
  · set ψ : Matrix (Fin m) (Fin m) ℂ → ℂ := fun Y =>
      unitsExtension F (iota Y * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) *
        (normSqC Y.det)⁻¹ with hψ
    refine contMDiff_of_contDiffOn (ψ := ψ) ?_ fun g => ?_
    · intro Y hY
      have hY' : IsUnit Y := hY
      have hdet : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY').ne_zero
      refine ContDiffAt.contDiffWithinAt (ContDiffAt.mul ?_ ?_)
      · have hmul : ContDiff ℝ ∞ fun Y : Matrix (Fin m) (Fin m) ℂ =>
            iota Y * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
          contDiff_iota.mul contDiff_const
        have hunit : IsUnit (iota Y * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) := by
          rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, det_iota]
          exact (isUnit_iff_ne_zero.mpr hdet).mul
            (Matrix.isUnit_iff_isUnit_det _ |>.mp (Units.isUnit y))
        exact ((contDiffOn_unitsExtension hF.1).contDiffAt
          (isOpen_setOf_isUnit_matrix.mem_nhds hunit)).comp Y hmul.contDiffAt
      · have hn : ContDiff ℝ ∞ fun Y : Matrix (Fin m) (Fin m) ℂ => ‖Y.det‖ ^ 2 :=
          (contDiff_norm_sq ℝ).comp contDiff_det
        have hne : ‖Y.det‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hdet)
        have := Complex.ofRealCLM.contDiff.contDiffAt.comp Y (hn.contDiffAt.inv hne)
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)
        simp [normSqC]
    · simp only [hψ, leviSlice]
      rw [← iotaGL_val, ← Units.val_mul, unitsExtension_val]
  · rw [principalSeriesCharacter_modulus]
    exact leviSlice_covariant hF y a u g

/-! ## The `U(m)`-average -/

section Natural

/-- `F^♮(x) = ∫_{U(m)} F(ι(k) x) dk`. -/
def natural (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (x : Langlands.GeneralLinear (m + 1) ℂ) :
    ℂ :=
  ∫ k : unitaryCompact ℂ m, F (iotaGL (k : Langlands.GeneralLinear m ℂ) * x) ∂unitaryHaar m

theorem normSqC_det_unitary {n : ℕ} (k : unitaryCompact ℂ n) :
    normSqC ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  have h := congrArg Matrix.det (ComplexLastRowIntegral.mul_conjTranspose_eq_one k)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  unfold normSqC
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm]
  exact h

variable {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
  (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1)))

include hF in
/-- Levi equivariance: `F^♮(ι(A) y) = |det A|² F^♮(y)`. -/
theorem natural_iota_mul (A : Langlands.GeneralLinear m ℂ)
    (y : Langlands.GeneralLinear (m + 1) ℂ) :
    natural F (iotaGL A * y) = normSqC (A : Matrix (Fin m) (Fin m) ℂ).det * natural F y := by
  have hinv := integral_mul_eq (leviSlice_mem hF y) A
  have hA : normSqC (A : Matrix (Fin m) (Fin m) ℂ).det ≠ 0 :=
    normSqC_ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)).ne_zero
  have h1 : ∀ k : unitaryCompact ℂ m, leviSlice F y ((k : Langlands.GeneralLinear m ℂ) * A) =
      F (iotaGL (k : Langlands.GeneralLinear m ℂ) * (iotaGL A * y)) *
        (normSqC (A : Matrix (Fin m) (Fin m) ℂ).det)⁻¹ := by
    intro k
    unfold leviSlice
    rw [map_mul, mul_assoc, Units.val_mul, Matrix.det_mul, normSqC_mul, normSqC_det_unitary,
      one_mul]
  have h2 : ∀ k : unitaryCompact ℂ m, leviSlice F y (k : Langlands.GeneralLinear m ℂ) =
      F (iotaGL (k : Langlands.GeneralLinear m ℂ) * y) := by
    intro k
    unfold leviSlice
    rw [normSqC_det_unitary]
    simp
  rw [integral_congr_ae (ae_of_all _ h1), integral_congr_ae (ae_of_all _ h2),
    integral_mul_const] at hinv
  unfold natural
  rw [← hinv]
  field_simp

/-- `d(a)` as an element of `GL_{m+1}(ℂ)`. -/
def dlastGL (a : ℂˣ) : Langlands.GeneralLinear (m + 1) ℂ :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits fun i => Fin.lastCases a (fun _ => 1) i

theorem dlastGL_val (a : ℂˣ) :
    ((dlastGL (m := m) a : Langlands.GeneralLinear (m + 1) ℂ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = dlast (a : ℂ) := by
  rw [dlastGL, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, dlast]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp

theorem modulusValue_dlast (a : ℂˣ) :
    modulusValue (m + 1) (fun i => Fin.lastCases a (fun _ => 1) i) =
      normSqC (a : ℂ) ^ (-(m : ℂ)) := by
  rw [modulusValue, Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Units.val_one, normSqC_one,
    Complex.one_cpow, Finset.prod_const_one, one_mul, Fin.val_last]
  congr 1
  push_cast
  ring

include hF in
theorem natural_dlast_mul (a : ℂˣ) (x : Langlands.GeneralLinear (m + 1) ℂ) :
    natural F (dlastGL a * x) = normSqC (a : ℂ) ^ (-(m : ℂ)) * natural F x := by
  unfold natural
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  have hcomm : iotaGL (k : Langlands.GeneralLinear m ℂ) * dlastGL a =
      dlastGL a * iotaGL (k : Langlands.GeneralLinear m ℂ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, iotaGL_val, dlastGL_val, iota_mul_dlast]
  have := covariant hF (fun i => Fin.lastCases a (fun _ => 1) i) 1
    (iotaGL (k : Langlands.GeneralLinear m ℂ) * x)
  rw [OneMemClass.coe_one, mul_one, modulusValue_dlast] at this
  show F (iotaGL (k : Langlands.GeneralLinear m ℂ) * (dlastGL a * x)) = _
  rw [← mul_assoc, hcomm, mul_assoc]
  exact this

/-- `n(c)` as an element of the upper unipotent group. -/
def nPU (c : Fin m → ℂ) : Langlands.GeneralLinear.upperUnipotent (m + 1) ℂ :=
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
theorem natural_nP_mul (c : Fin m → ℂ) (x : Langlands.GeneralLinear (m + 1) ℂ) :
    natural F ((nPU c : Langlands.GeneralLinear (m + 1) ℂ) * x) = natural F x := by
  unfold natural
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  have hcomm : iotaGL (k : Langlands.GeneralLinear m ℂ) *
      (nPU c : Langlands.GeneralLinear (m + 1) ℂ) =
      (nPU (((k : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) *ᵥ c) :
        Langlands.GeneralLinear (m + 1) ℂ) * iotaGL (k : Langlands.GeneralLinear m ℂ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, iotaGL_val]
    exact iota_mul_nP _ c
  simp only
  rw [← mul_assoc, hcomm, mul_assoc]
  exact covariant_upperUnipotent hF _ _

include hF in
/-- **`P_{m,1}`-equivariance of `F^♮`.** If the last row of `p` is `(0, …, 0, a)`, then
`F^♮(p x) = |det p|² (|a|²)^{-(m+1)} F^♮(x)`. -/
theorem natural_mul_lastRow (p : Langlands.GeneralLinear (m + 1) ℂ)
    (hp : ∀ j : Fin m, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j.castSucc = 0)
    (x : Langlands.GeneralLinear (m + 1) ℂ) :
    natural F (p * x) =
      normSqC (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det *
        normSqC ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) (Fin.last m)) ^
          (-((m : ℂ) + 1)) * natural F x := by
  set P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
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
  set AGL : Langlands.GeneralLinear m ℂ :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA)).unit with hAGL
  set aU : ℂˣ := Units.mk0 a ha with haU
  set c : Fin m → ℂ := fun i => P i.castSucc (Fin.last m) / a with hc
  have hdec : p = (nPU c : Langlands.GeneralLinear (m + 1) ℂ) * iotaGL AGL * dlastGL aU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, iotaGL_val, dlastGL_val]
    exact eq_nP_mul_iota_mul_dlast hp ha
  have hAval : (AGL : Matrix (Fin m) (Fin m) ℂ) = topLeft P := IsUnit.unit_spec _
  rw [hdec, mul_assoc, mul_assoc, natural_nP_mul hF, natural_iota_mul hF,
    natural_dlast_mul hF, hAval]
  have haC : normSqC a ≠ 0 := normSqC_ne_zero ha
  have hpow : normSqC a ^ (-((m : ℂ) + 1)) = normSqC a ^ (-(m : ℂ)) * (normSqC a)⁻¹ := by
    unfold normSqC at haC ⊢
    rw [neg_add, Complex.cpow_add _ _ haC, Complex.cpow_neg_one]
  change _ = normSqC P.det * normSqC a ^ (-((m : ℂ) + 1)) * _
  rw [hpow, hdetP, normSqC_mul]
  have hcoe : ((aU : ℂˣ) : ℂ) = a := rfl
  rw [hcoe]
  field_simp
  rfl

end Natural

/-! ### The chart matrices `J(r)` -/

/-- `J(r)`: the identity matrix with last row replaced by `r`. -/
def Jmat (r : Fin (m + 1) → ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun i j => Fin.lastCases (r j)
    (fun i' => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i'.castSucc j) i

theorem Jmat_isLowerTriangular (r : Fin (m + 1) → ℂ) : (Jmat r).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  have hi : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
  obtain ⟨i', rfl⟩ : ∃ i', i = i'.castSucc := ⟨i.castPred hi, by simp⟩
  simp only [Jmat, Matrix.of_apply, Fin.lastCases_castSucc]
  exact Matrix.one_apply_ne (ne_of_lt hij)

theorem det_Jmat (r : Fin (m + 1) → ℂ) : (Jmat r).det = r (Fin.last m) := by
  rw [Matrix.det_of_isLowerTriangular _ (Jmat_isLowerTriangular r), Fin.prod_univ_castSucc]
  simp [Jmat]

/-- `J(r)` as an element of `GL_{m+1}(ℂ)` when `r_m ≠ 0`. -/
def JGL (r : Fin (m + 1) → ℂ) (hr : r (Fin.last m) ≠ 0) : Langlands.GeneralLinear (m + 1) ℂ :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Jmat]; exact isUnit_iff_ne_zero.mpr hr)).unit

theorem JGL_val (r : Fin (m + 1) → ℂ) (hr : r (Fin.last m) ≠ 0) :
    ((JGL r hr : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      Jmat r := IsUnit.unit_spec _

theorem Jmat_smul (s : ℂ) (r : Fin (m + 1) → ℂ) : Jmat (s • r) = dlast s * Jmat r := by
  ext i j
  rw [dlast, Matrix.diagonal_mul]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp [Jmat]

section Chart

variable {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
  (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1)))

include hF in
/-- `F^♮(J(s r)) = (|s|²)^{-m} F^♮(J(r))`. -/
theorem natural_Jmat_smul {s : ℂ} (hs : s ≠ 0) (r : Fin (m + 1) → ℂ) (hr : r (Fin.last m) ≠ 0)
    (hsr : (s • r) (Fin.last m) ≠ 0) :
    natural F (JGL (s • r) hsr) = normSqC s ^ (-(m : ℂ)) * natural F (JGL r hr) := by
  have h : JGL (s • r) hsr = dlastGL (Units.mk0 s hs) * JGL r hr := by
    apply Units.ext
    rw [Units.val_mul, JGL_val, JGL_val, dlastGL_val, Units.val_mk0, Jmat_smul]
  rw [h, natural_dlast_mul hF, Units.val_mk0]

theorem mul_conjTranspose_one {n : ℕ} (κ : unitaryCompact ℂ n) :
    ((κ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) *
      ((κ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
  ComplexLastRowIntegral.mul_conjTranspose_eq_one κ

include hF in
/-- For `κ ∈ U(m+1)` with last row `r`, `r_m ≠ 0`: `F^♮(J(r)) = |r_m|² F^♮(κ)`. -/
theorem natural_Jmat_lastRow (κ : unitaryCompact ℂ (m + 1))
    (hr : ComplexLastRowIntegral.lastRow κ (Fin.last m) ≠ 0) :
    natural F (JGL (ComplexLastRowIntegral.lastRow κ) hr) =
      normSqC (ComplexLastRowIntegral.lastRow κ (Fin.last m)) *
        natural F (κ : Langlands.GeneralLinear (m + 1) ℂ) := by
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    ((κ : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) with hK
  have hKK : K * Kᴴ = 1 := mul_conjTranspose_one κ
  set p : Langlands.GeneralLinear (m + 1) ℂ :=
    JGL (ComplexLastRowIntegral.lastRow κ) hr * (κ : Langlands.GeneralLinear (m + 1) ℂ)⁻¹
    with hpdef
  have hinvK : (((κ : Langlands.GeneralLinear (m + 1) ℂ)⁻¹ : Langlands.GeneralLinear (m + 1) ℂ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = Kᴴ := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hKK]
  have hlast : ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j := by
    intro j
    rw [hpdef, Units.val_mul, JGL_val, hinvK, ← hKK]
    simp [Jmat, Matrix.mul_apply, ComplexLastRowIntegral.lastRow, hK]
  have hp : ∀ j : Fin m, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j.castSucc = 0 :=
    fun j => by rw [hlast, Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm]
  have hpl : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) (Fin.last m) = 1 := by
    rw [hlast, Matrix.one_apply_eq]
  have hdet : normSqC (p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det =
      normSqC (ComplexLastRowIntegral.lastRow κ (Fin.last m)) := by
    rw [hpdef, Units.val_mul, JGL_val, Matrix.det_mul, det_Jmat, normSqC_mul, hinvK,
      Matrix.det_conjTranspose]
    have h1 : normSqC (star K.det) = 1 := by
      have := normSqC_det_unitary κ
      unfold normSqC at this ⊢
      rw [norm_star]
      exact this
    rw [h1, mul_one]
  have hJ : JGL (ComplexLastRowIntegral.lastRow κ) hr =
      p * (κ : Langlands.GeneralLinear (m + 1) ℂ) := by
    rw [hpdef, inv_mul_cancel_right]
  rw [hJ, natural_mul_lastRow hF p hp, hpl, hdet, normSqC_one, Complex.one_cpow, mul_one]

end Chart

/-! ### The homogeneous function of the last row -/

/-- The matrix-level average `Ñ(Y) = ∫_{U(m)} F̃(ι(k) Y) dk`, `F̃` the extension by zero. -/
def naturalMat (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ)
    (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : ℂ :=
  ∫ k : unitaryCompact ℂ m, unitsExtension F
    (iota ((k : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) * Y) ∂unitaryHaar m

theorem naturalMat_val (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ)
    (x : Langlands.GeneralLinear (m + 1) ℂ) :
    naturalMat F (x : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = natural F x := by
  unfold naturalMat natural
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only
  rw [← iotaGL_val, ← Units.val_mul, unitsExtension_val]

/-- `Φ(r) = F^♮(J(r)) |r_m|⁻² |r|^{2(m+1)}` (and `0` if `r_m = 0`). -/
def phiF (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (r : Fin (m + 1) → ℂ) : ℂ :=
  if r (Fin.last m) = 0 then 0 else
    naturalMat F (Jmat r) * (normSqC (r (Fin.last m)))⁻¹ *
      ((ComplexLastRowIntegral.sqNorm r ^ (m + 1) : ℝ) : ℂ)

theorem phiF_eq (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (r : Fin (m + 1) → ℂ)
    (hr : r (Fin.last m) ≠ 0) :
    phiF F r = natural F (JGL r hr) * (normSqC (r (Fin.last m)))⁻¹ *
      ((ComplexLastRowIntegral.sqNorm r ^ (m + 1) : ℝ) : ℂ) := by
  rw [phiF, ite_eq_right hr, ← JGL_val r hr, naturalMat_val]

section Phi

variable {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
  (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1)))

include hF in
theorem phiF_homogeneous : ComplexLastRowIntegral.IsHomogeneousZero (phiF F) := by
  intro s hs r
  by_cases hr : r (Fin.last m) = 0
  · have hsr : (s • r) (Fin.last m) = 0 := by simp [hr]
    rw [phiF, ite_eq_left hsr, phiF, ite_eq_left hr]
  · have hsr : (s • r) (Fin.last m) ≠ 0 := by simp [hs, hr]
    rw [phiF_eq _ _ hsr, phiF_eq _ _ hr, natural_Jmat_smul hF hs r hr hsr,
      ComplexLastRowIntegral.sqNorm_smul]
    simp only [Pi.smul_apply, smul_eq_mul, normSqC_mul]
    have hsC : normSqC s ≠ 0 := normSqC_ne_zero hs
    have hrC : normSqC (r (Fin.last m)) ≠ 0 := normSqC_ne_zero hr
    have hpow : normSqC s ^ (-(m : ℂ)) = (normSqC s ^ m)⁻¹ := by
      rw [Complex.cpow_neg, Complex.cpow_natCast]
    rw [hpow]
    have hs' : ((‖s‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hs
    have hr' : ((‖r (Fin.last m)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hr
    unfold normSqC at hsC hrC ⊢
    push_cast
    field_simp
    ring

theorem sqNorm_lastRow (κ : unitaryCompact ℂ (m + 1)) :
    ComplexLastRowIntegral.sqNorm (ComplexLastRowIntegral.lastRow κ) = 1 := by
  have h := congrFun (congrFun (mul_conjTranspose_one κ) (Fin.last m)) (Fin.last m)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ((ComplexLastRowIntegral.sqNorm (ComplexLastRowIntegral.lastRow κ) : ℝ) : ℂ) = 1 := by
    rw [← h, ComplexLastRowIntegral.ofReal_sqNorm]
    simp [dotProduct, ComplexLastRowIntegral.lastRow, Matrix.conjTranspose_apply]
  exact_mod_cast h2

include hF in
theorem phiF_lastRow (κ : unitaryCompact ℂ (m + 1))
    (hr : ComplexLastRowIntegral.lastRow κ (Fin.last m) ≠ 0) :
    phiF F (ComplexLastRowIntegral.lastRow κ) =
      natural F (κ : Langlands.GeneralLinear (m + 1) ℂ) := by
  rw [phiF_eq _ _ hr, natural_Jmat_lastRow hF κ hr, sqNorm_lastRow, one_pow]
  have hrC : normSqC (ComplexLastRowIntegral.lastRow κ (Fin.last m)) ≠ 0 := normSqC_ne_zero hr
  push_cast
  field_simp

include hF in
theorem exists_bound_phiF : ∃ C, ∀ r, ‖phiF F r‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hF.1.continuous.comp continuous_subtype_val :
      Continuous fun κ : unitaryCompact ℂ (m + 1) => F κ).continuousOn)
  have hnat : ∀ κ : unitaryCompact ℂ (m + 1),
      ‖natural F (κ : Langlands.GeneralLinear (m + 1) ℂ)‖ ≤ C := by
    intro κ
    have h := norm_integral_le_of_norm_le_const (μ := unitaryHaar m) (C := C)
      (f := fun k : unitaryCompact ℂ m =>
        F (iotaGL (k : Langlands.GeneralLinear m ℂ) * (κ : Langlands.GeneralLinear (m + 1) ℂ)))
      (ae_of_all _ fun k => hC ⟨_, mul_mem (iotaGL_mem_unitaryCompact k.2) κ.2⟩ trivial)
    rw [probReal_univ, mul_one] at h
    exact h
  refine ⟨max C 0, fun r => ?_⟩
  by_cases hr : r (Fin.last m) = 0
  · rw [phiF, ite_eq_left hr, norm_zero]
    exact le_max_right _ _
  · have hq : 0 < ComplexLastRowIntegral.sqNorm r := by
      have : 0 < ‖r (Fin.last m)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hr) 2
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖r j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ _))
    set t := Real.sqrt (ComplexLastRowIntegral.sqNorm r) with ht
    have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    set u := ((t⁻¹ : ℝ) : ℂ) • r with hu
    have hu1 : ComplexLastRowIntegral.sqNorm u = 1 := by
      rw [hu, ComplexLastRowIntegral.sqNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        inv_pow, sq_abs, ht, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']
    obtain ⟨K₀, hK₀, hlast⟩ := ComplexLastRowIntegral.exists_unitary_lastRow u hu1
    have hK₀mem : K₀ ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact hK₀
    let κ₀ : unitaryCompact ℂ (m + 1) := ⟨Unitary.toUnits ⟨K₀, hK₀mem⟩, hK₀mem⟩
    have hrow : ComplexLastRowIntegral.lastRow κ₀ = u := hlast
    have hul : ComplexLastRowIntegral.lastRow κ₀ (Fin.last m) ≠ 0 := by
      rw [hrow, hu, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (by exact_mod_cast inv_ne_zero ht0) hr
    have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hrt : r = (t : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht0, Complex.ofReal_one, one_smul]
    rw [hrt, phiF_homogeneous hF (t : ℂ) ht0', ← hrow, phiF_lastRow hF κ₀ hul]
    exact le_trans (hnat κ₀) (le_max_left _ _)

end Phi

theorem measurable_unitsExtension {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hFs : ContMDiff (matrixModel ℂ (m + 1)) 𝓘(ℝ, ℂ) ∞ F) : Measurable (unitsExtension F) := by
  classical
  have h : unitsExtension F = {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ | IsUnit Y}.piecewise
      (unitsExtension F) (fun _ => 0) := by
    funext Y
    by_cases hY : IsUnit Y
    · simp [Set.piecewise, hY]
    · simp [Set.piecewise, hY, unitsExtension]
  rw [h]
  exact ContinuousOn.measurable_piecewise (contDiffOn_unitsExtension hFs).continuousOn
    continuousOn_const isOpen_setOf_isUnit_matrix.measurableSet

theorem measurable_iota_mul_Jmat :
    Measurable fun p : (Fin (m + 1) → ℂ) × unitaryCompact ℂ m =>
      iota ((p.2 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) * Jmat p.1 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have hform : (fun p : (Fin (m + 1) → ℂ) × unitaryCompact ℂ m =>
      (iota ((p.2 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) * Jmat p.1) i j) =
      fun p => ∑ l, iota ((p.2 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) i l *
        Jmat p.1 l j := funext fun p => rfl
  rw [hform]
  refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
  · have hc : Continuous fun k : unitaryCompact ℂ m =>
        iota ((k : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) i l :=
      (continuous_apply l).comp ((continuous_apply i).comp
        (contDiff_iota.continuous.comp ComplexLastRowIntegral.continuous_unitaryCompact_val))
    exact hc.measurable.comp measurable_snd
  · induction l using Fin.lastCases with
    | last =>
      have : (fun p : (Fin (m + 1) → ℂ) × unitaryCompact ℂ m => Jmat p.1 (Fin.last m) j) =
          fun p => p.1 j := funext fun p => by simp [Jmat]
      rw [this]
      exact (measurable_pi_apply j).comp measurable_fst
    | cast l' =>
      have : (fun p : (Fin (m + 1) → ℂ) × unitaryCompact ℂ m => Jmat p.1 l'.castSucc j) =
          fun _ => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) l'.castSucc j :=
        funext fun p => by simp [Jmat]
      rw [this]
      exact measurable_const

theorem measurable_phiF {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hFs : ContMDiff (matrixModel ℂ (m + 1)) 𝓘(ℝ, ℂ) ∞ F) : Measurable (phiF F) := by
  unfold phiF
  refine Measurable.ite (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
    measurable_const ?_
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · have hj : Measurable fun p : (Fin (m + 1) → ℂ) × unitaryCompact ℂ m => unitsExtension F
        (iota ((p.2 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) * Jmat p.1) :=
      (measurable_unitsExtension hFs).comp measurable_iota_mul_Jmat
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := unitaryHaar m)).measurable
  · have hc : Continuous fun r : Fin (m + 1) → ℂ => normSqC (r (Fin.last m)) := by
      unfold normSqC
      fun_prop
    exact hc.measurable.inv
  · have hc : Continuous fun r : Fin (m + 1) → ℂ =>
        ((ComplexLastRowIntegral.sqNorm r ^ (m + 1) : ℝ) : ℂ) := by
      have := ComplexLastRowIntegral.continuous_sqNorm (m := m + 1)
      fun_prop
    exact hc.measurable

/-- The last diagonal entry of a Haar-random unitary matrix is almost surely nonzero. -/
theorem ae_lastRow_last_ne_zero :
    ∀ᵐ κ ∂unitaryHaar (m + 1), ComplexLastRowIntegral.lastRow κ (Fin.last m) ≠ 0 := by
  classical
  set Φ₀ : (Fin (m + 1) → ℂ) → ℂ := fun x => if x (Fin.last m) = 0 then 1 else 0 with hΦ₀
  have hmeas : Measurable Φ₀ :=
    Measurable.ite (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
      measurable_const measurable_const
  have hbound : ∀ x, ‖Φ₀ x‖ ≤ 1 := fun x => by
    by_cases h : x (Fin.last m) = 0 <;> simp [hΦ₀, h]
  have hhom : ComplexLastRowIntegral.IsHomogeneousZero Φ₀ := by
    intro s hs x
    simp [hΦ₀, hs]
  have h := ComplexLastRowIntegral.integral_lastRow hmeas hbound hhom
  have hzero : ∀ v : Fin m → ℂ,
      Φ₀ (Fin.snoc v 1) * (ComplexLastRowIntegral.chartWeight v : ℂ) = 0 :=
    fun v => by simp [hΦ₀]
  simp only [hzero, integral_zero, mul_zero] at h
  set g : unitaryCompact ℂ (m + 1) → ℝ := fun κ =>
    if ComplexLastRowIntegral.lastRow κ (Fin.last m) = 0 then 1 else 0 with hg
  have hgC : (fun κ => Φ₀ (ComplexLastRowIntegral.lastRow κ)) = fun κ => ((g κ : ℝ) : ℂ) := by
    funext κ
    by_cases hκ : ComplexLastRowIntegral.lastRow κ (Fin.last m) = 0 <;> simp [hΦ₀, hg, hκ]
  rw [hgC, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hgc : Continuous fun κ : unitaryCompact ℂ (m + 1) =>
      ComplexLastRowIntegral.lastRow κ (Fin.last m) :=
    (continuous_apply (Fin.last m)).comp ((continuous_apply (Fin.last m)).comp
      ComplexLastRowIntegral.continuous_unitaryCompact_val)
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_eq_fun hgc.measurable measurable_const) measurable_const
      measurable_const
  have hgi : Integrable g (unitaryHaar (m + 1)) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun κ => by
      by_cases hκ : ComplexLastRowIntegral.lastRow κ (Fin.last m) = 0 <;> simp [hg, hκ])
  have hae := (integral_eq_zero_iff_of_nonneg (fun κ => by
    by_cases hκ : ComplexLastRowIntegral.lastRow κ (Fin.last m) = 0 <;> simp [hg, hκ]) hgi).mp h
  filter_upwards [hae] with κ hκ
  intro h0
  simp [hg, h0] at hκ

/-- `∫_{U(m+1)} F = ∫_{U(m+1)} F^♮`. -/
theorem integral_eq_integral_natural {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hFs : ContMDiff (matrixModel ℂ (m + 1)) 𝓘(ℝ, ℂ) ∞ F) :
    ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1) =
      ∫ κ, natural F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hFs.continuous.comp continuous_subtype_val :
      Continuous fun κ : unitaryCompact ℂ (m + 1) => F κ).continuousOn)
  set G : unitaryCompact ℂ m × unitaryCompact ℂ (m + 1) → ℂ := fun p =>
    F (iotaGL (p.1 : Langlands.GeneralLinear m ℂ) * (p.2 : Langlands.GeneralLinear (m + 1) ℂ))
    with hGdef
  have hGm : Measurable G := by
    have hform : G = fun p => unitsExtension F
        (iota ((p.1 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) *
          ((p.2 : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) := by
      funext p
      rw [hGdef]
      simp only
      rw [← iotaGL_val, ← Units.val_mul, unitsExtension_val]
    rw [hform]
    refine (measurable_unitsExtension hFs).comp ?_
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    have hform2 : (fun p : unitaryCompact ℂ m × unitaryCompact ℂ (m + 1) =>
        (iota ((p.1 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) *
          ((p.2 : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) i j) =
        fun p => ∑ l, iota ((p.1 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) i l *
          ((p.2 : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) l j :=
      funext fun p => rfl
    rw [hform2]
    refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
    · exact ((continuous_apply l).comp ((continuous_apply i).comp
        (contDiff_iota.continuous.comp
          ComplexLastRowIntegral.continuous_unitaryCompact_val))).measurable.comp measurable_fst
    · exact ((continuous_apply j).comp ((continuous_apply l).comp
        ComplexLastRowIntegral.continuous_unitaryCompact_val)).measurable.comp measurable_snd
  have hGi : Integrable G ((unitaryHaar m).prod (unitaryHaar (m + 1))) :=
    Integrable.of_bound hGm.aestronglyMeasurable C (ae_of_all _ fun p =>
      hC ⟨_, mul_mem (iotaGL_mem_unitaryCompact p.1.2) p.2.2⟩ trivial)
  have hleft : ∀ k : unitaryCompact ℂ m,
      ∫ κ, G (k, κ) ∂unitaryHaar (m + 1) =
        ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1) :=
    fun k => integral_mul_left_eq_self (μ := unitaryHaar (m + 1))
      (fun κ : unitaryCompact ℂ (m + 1) => F (κ : Langlands.GeneralLinear (m + 1) ℂ)) (iotaK k)
  calc ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1)
      = ∫ k : unitaryCompact ℂ m, (∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ)
          ∂unitaryHaar (m + 1)) ∂unitaryHaar m := by
        rw [integral_const, probReal_univ, one_smul]
    _ = ∫ k : unitaryCompact ℂ m, (∫ κ, G (k, κ) ∂unitaryHaar (m + 1)) ∂unitaryHaar m :=
        integral_congr_ae (ae_of_all _ fun k => (hleft k).symm)
    _ = ∫ κ, ∫ k, G (k, κ) ∂unitaryHaar m ∂unitaryHaar (m + 1) :=
        integral_integral_swap (f := fun k κ => G (k, κ)) hGi
    _ = ∫ κ, natural F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1) := rfl

theorem snoc_last_ne_zero (v : Fin m → ℂ) : (Fin.snoc v 1 : Fin (m + 1) → ℂ) (Fin.last m) ≠ 0 := by
  simp

/-- The chart point `J(v, 1)`: the identity matrix with last row replaced by `(v, 1)`. -/
def chartGL (v : Fin m → ℂ) : Langlands.GeneralLinear (m + 1) ℂ :=
  JGL (Fin.snoc v 1) (snoc_last_ne_zero v)

theorem phiF_snoc (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (v : Fin m → ℂ) :
    phiF F (Fin.snoc v 1) * (ComplexLastRowIntegral.chartWeight v : ℂ) =
      natural F (chartGL v) := by
  rw [phiF_eq _ _ (snoc_last_ne_zero v), ComplexLastRowIntegral.sqNorm_snoc, Fin.snoc_last,
    ComplexLastRowIntegral.chartWeight, chartGL, normSqC_one, inv_one, mul_one]
  have hq : 0 < 1 + ComplexLastRowIntegral.sqNorm v := by
    linarith [ComplexLastRowIntegral.sqNorm_nonneg v]
  have hpos : ((1 + ComplexLastRowIntegral.sqNorm v) ^ (m + 1) : ℝ) ≠ 0 :=
    (pow_pos hq _).ne'
  have hpos' : (((1 + ComplexLastRowIntegral.sqNorm v) ^ (m + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos
  rw [norm_one, one_pow, add_comm (ComplexLastRowIntegral.sqNorm v) 1, Complex.ofReal_inv,
    mul_assoc, mul_inv_cancel₀ hpos', mul_one]

/-- The normalizing constant
`c_m = (∫_ℂ |t|^(2m) e^{-|t|²} dt) / (∫_{ℂ^{m+1}} e^{-|x|²} dx)`. -/
def chartConstant (m : ℕ) : ℝ :=
  ComplexLastRowIntegral.gaussianMoment m /
    ∫ x : Fin (m + 1) → ℂ, ComplexLastRowIntegral.gaussian x

theorem gaussianMoment_pos (m : ℕ) : 0 < ComplexLastRowIntegral.gaussianMoment m := by
  unfold ComplexLastRowIntegral.gaussianMoment
  have hint : Integrable (fun t : ℂ => ‖t‖ ^ (2 * m) * Real.exp (-‖t‖ ^ 2)) := by
    have := ComplexLastRowIntegral.integrable_norm_pow_mul_exp m (a := 1) one_pos
    simpa using this
  rw [integral_pos_iff_support_of_nonneg (fun t => by positivity) hint]
  have hsub : {t : ℂ | t ≠ 0} ⊆
      Function.support (fun t : ℂ => ‖t‖ ^ (2 * m) * Real.exp (-‖t‖ ^ 2)) := by
    intro t ht
    simp only [Function.mem_support]
    exact (mul_pos (pow_pos (norm_pos_iff.mpr ht) _) (Real.exp_pos _)).ne'
  have hopen : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨1, one_ne_zero⟩) (measure_mono hsub)

theorem chartConstant_pos (m : ℕ) : 0 < chartConstant m :=
  div_pos (gaussianMoment_pos m) ComplexLastRowIntegral.integral_gaussian_pos

/-- **Maximal-parabolic integration formula.**
`∫_{U(m+1)} F = c_m ∫_{ℂ^m} ∫_{U(m)} F(ι(k) J(v, 1)) dk dv`. -/
theorem integral_eq_chart {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1))) :
    ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1) =
      (chartConstant m : ℂ) * ∫ v : Fin m → ℂ, natural F (chartGL v) := by
  rw [integral_eq_integral_natural hF.1]
  have hae : (fun κ : unitaryCompact ℂ (m + 1) =>
      natural F (κ : Langlands.GeneralLinear (m + 1) ℂ))
      =ᵐ[unitaryHaar (m + 1)] fun κ => phiF F (ComplexLastRowIntegral.lastRow κ) := by
    filter_upwards [ae_lastRow_last_ne_zero] with κ hκ
    exact (phiF_lastRow hF κ hκ).symm
  rw [integral_congr_ae hae]
  obtain ⟨C, hC⟩ := exists_bound_phiF hF
  rw [ComplexLastRowIntegral.integral_lastRow (measurable_phiF hF.1) hC (phiF_homogeneous hF),
    chartConstant]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun v => phiF_snoc F v)

end ComplexMaximalParabolicIntegration

open ComplexMaximalParabolicIntegration ComplexDuality

/-- **Statement (the `U(m+1)`-integral in coordinates of the maximal parabolic `P_{m,1}`).**
Let `F` be in the smooth principal series of `GL_{m+1}(ℂ)` of the characters
`z ↦ (|z|²)^(m/2 - i)` (`ComplexKIntegralInvariance.modulusCharacter (m+1)`), i.e. `F` is smooth and
`F(diag(a) u g) = ∏ᵢ |aᵢ|^{2(m - 2i)} F(g)` for `a ∈ (ℂˣ)^{m+1}`, `u` upper unipotent: `F` lies in the
principal series of the modulus character `δ_B`. Then, with Haar probability measures,
`∫_{U(m+1)} F(κ) dκ = c_m ∫_{ℂ^m} ∫_{U(m)} F(ι(k) J(v, 1)) dk dv`,
where `ι(k) = diag(k, 1)`, `J(v, 1)` is the identity matrix with last row `(v, 1)`, and
`c_m = (∫_ℂ |t|^{2m} e^{-|t|²} dt) / (∫_{ℂ^{m+1}} e^{-∑ |xᵢ|²} dx) > 0`. -/
def ComplexMaximalParabolicIntegrationStatement : Prop :=
  ∀ (m : ℕ) (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ),
    F ∈ principalSeries ℂ (m + 1) (ComplexKIntegralInvariance.modulusCharacter (m + 1)) →
      ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1) =
        (((∫ t : ℂ, ‖t‖ ^ (2 * m) * Real.exp (-‖t‖ ^ 2)) /
            ∫ x : Fin (m + 1) → ℂ, Real.exp (-∑ i, ‖x i‖ ^ 2) : ℝ) : ℂ) *
          ∫ v : Fin m → ℂ, ∫ k : unitaryCompact ℂ m,
            F (iotaGL (k : Langlands.GeneralLinear m ℂ) * chartGL v) ∂unitaryHaar m

theorem complexMaximalParabolicIntegration : ComplexMaximalParabolicIntegrationStatement :=
  fun _ _ hF => integral_eq_chart hF

end Langlands.Archimedean
