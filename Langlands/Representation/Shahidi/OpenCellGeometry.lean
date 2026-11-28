import Langlands.Representation.Shahidi.UnramifiedOpenCellSumStatement

/-! # Geometry of the two-block open cell

Block computations for `w u'(Y) = lower(Y) w` and the parabolic factorization of
`lower(Y) = [[I_m, 0], [Y, I_n]]`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Matrix

universe u

section Ring

variable (m n : ℕ) (R : Type*) [CommRing R]

/-- `w u'(Y) = lower(Y) w`. -/
theorem blockWeyl_mul_intertwiningUnipotent (Y : Matrix (Fin n) (Fin m) R) :
    blockWeyl m n R * intertwiningUnipotent m n R Y = lower m n R Y * blockWeyl m n R := by
  rw [lower, inv_mul_cancel_right]

/-- Entries of a product in `GL_(m+n)` split along the two blocks. -/
theorem mul_apply_split (g h : Langlands.GeneralLinear (m + n) R) (i j : Fin (m + n)) :
    (g * h) i j = (∑ l : Fin m, g i (l.castAdd n) * h (l.castAdd n) j) +
      ∑ l : Fin n, g i (l.natAdd m) * h (l.natAdd m) j := by
  change ((g : Matrix (Fin (m + n)) (Fin (m + n)) R) * h) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_add]

end Ring

end Langlands.Shahidi.OpenCell

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Matrix

section Blocks

variable {m n : ℕ} {R : Type*} [CommRing R]

theorem castAdd_lt_natAdd (i : Fin m) (j : Fin n) : (i.castAdd n : Fin (m + n)) < j.natAdd m := by
  rw [Fin.lt_def]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- The inverse of an invertible upper triangular matrix is upper triangular. -/
theorem inv_isUpperTriangular {k : ℕ} (b : Matrix.GeneralLinearGroup (Fin k) R)
    (hb : b.val.IsUpperTriangular) : (b⁻¹).val.IsUpperTriangular := by
  let := b.invertible
  simpa only [Matrix.GeneralLinearGroup.coe_inv] using
    Matrix.blockTriangular_inv_of_blockTriangular hb

theorem lowerLeft_eq_zero {b : Langlands.GeneralLinear (m + n) R}
    (hb : b.val.IsUpperTriangular) (i : Fin n) (j : Fin m) :
    b (i.natAdd m) (j.castAdd n) = 0 :=
  hb (castAdd_lt_natAdd j i)

theorem sum_topLeft_mul {b c : Langlands.GeneralLinear (m + n) R}
    (hc : c.val.IsUpperTriangular) (i j : Fin m) :
    ∑ l : Fin m, b (i.castAdd n) (l.castAdd n) * c (l.castAdd n) (j.castAdd n) =
      (b * c) (i.castAdd n) (j.castAdd n) := by
  rw [mul_apply_split]
  simp [lowerLeft_eq_zero hc]

theorem sum_botRight_mul {b c : Langlands.GeneralLinear (m + n) R}
    (hb : b.val.IsUpperTriangular) (i j : Fin n) :
    ∑ l : Fin n, b (i.natAdd m) (l.natAdd m) * c (l.natAdd m) (j.natAdd m) =
      (b * c) (i.natAdd m) (j.natAdd m) := by
  rw [mul_apply_split]
  simp [lowerLeft_eq_zero hb]

/-- The top-left diagonal block of an invertible upper triangular matrix. -/
def topLeft (b : Langlands.GeneralLinear (m + n) R) (hb : b.val.IsUpperTriangular) :
    Langlands.GeneralLinear m R where
  val := Matrix.of fun i j => b (i.castAdd n) (j.castAdd n)
  inv := Matrix.of fun i j => b⁻¹ (i.castAdd n) (j.castAdd n)
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [sum_topLeft_mul (inv_isUpperTriangular b hb), mul_inv_cancel]
    simp [Matrix.one_apply]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [sum_topLeft_mul hb, inv_mul_cancel]
    simp [Matrix.one_apply]

/-- The bottom-right diagonal block of an invertible upper triangular matrix. -/
def botRight (b : Langlands.GeneralLinear (m + n) R) (hb : b.val.IsUpperTriangular) :
    Langlands.GeneralLinear n R where
  val := Matrix.of fun i j => b (i.natAdd m) (j.natAdd m)
  inv := Matrix.of fun i j => b⁻¹ (i.natAdd m) (j.natAdd m)
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [sum_botRight_mul hb, mul_inv_cancel]
    simp [Matrix.one_apply]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [sum_botRight_mul (inv_isUpperTriangular b hb), inv_mul_cancel]
    simp [Matrix.one_apply]

@[simp] theorem topLeft_apply (b : Langlands.GeneralLinear (m + n) R)
    (hb : b.val.IsUpperTriangular) (i j : Fin m) :
    topLeft b hb i j = b (i.castAdd n) (j.castAdd n) := rfl

@[simp] theorem botRight_apply (b : Langlands.GeneralLinear (m + n) R)
    (hb : b.val.IsUpperTriangular) (i j : Fin n) :
    botRight b hb i j = b (i.natAdd m) (j.natAdd m) := rfl

theorem topLeft_inv_apply (b : Langlands.GeneralLinear (m + n) R)
    (hb : b.val.IsUpperTriangular) (i j : Fin m) :
    (topLeft b hb)⁻¹ i j = b⁻¹ (i.castAdd n) (j.castAdd n) := rfl

theorem botRight_inv_apply (b : Langlands.GeneralLinear (m + n) R)
    (hb : b.val.IsUpperTriangular) (i j : Fin n) :
    (botRight b hb)⁻¹ i j = b⁻¹ (i.natAdd m) (j.natAdd m) := rfl

/-- The upper-right coordinate of the parabolic factorization. -/
def radicalCoordinate (b : Langlands.GeneralLinear (m + n) R) (hb : b.val.IsUpperTriangular) :
    Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j => ∑ l : Fin n, b (i.castAdd n) (l.natAdd m) * (botRight b hb)⁻¹ l j

/-- An invertible upper triangular matrix is `u(X) diag(b₁₁, b₂₂)`. -/
theorem eq_upper_mul_blockSum (b : Langlands.GeneralLinear (m + n) R)
    (hb : b.val.IsUpperTriangular) :
    b = upper m n R (radicalCoordinate b hb) * blockSum (topLeft b hb, botRight b hb) := by
  apply Units.ext
  ext i j
  rw [mul_apply_split]
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp
    | right j =>
      simp only [upper_first_first, upper_first_second, blockSum_apply_left_right,
        blockSum_apply_right, mul_zero, Finset.sum_const_zero, zero_add]
      simp only [radicalCoordinate, Matrix.of_apply, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      have key : ∀ l' : Fin n, ∑ l : Fin n, (botRight b hb)⁻¹ l' l * botRight b hb l j =
          if l' = j then 1 else 0 := by
        intro l'
        have h := congrArg (fun g : Langlands.GeneralLinear n R =>
          (g : Matrix (Fin n) (Fin n) R) l' j) (inv_mul_cancel (botRight b hb))
        simp only [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply] at h
        exact h
      simp_rw [← Finset.mul_sum, key]
      simp
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp [lowerLeft_eq_zero hb]
    | right j =>
      simp

end Blocks

section Lower

variable {m n : ℕ} {R : Type*} [CommRing R]

theorem lower_inv (Y : Matrix (Fin n) (Fin m) R) :
    (lower m n R Y)⁻¹ = lower m n R (-Y) := by
  rw [lower, lower, intertwiningUnipotent_neg]
  group

theorem lower_add (Y Z : Matrix (Fin n) (Fin m) R) :
    lower m n R (Y + Z) = lower m n R Y * lower m n R Z := by
  rw [lower, lower, lower, intertwiningUnipotent_add]
  group

/-- Right multiplication by `lower(Y)` keeps the columns of the second block. -/
theorem mul_lower_apply_natAdd (g : Langlands.GeneralLinear (m + n) R)
    (Y : Matrix (Fin n) (Fin m) R) (i : Fin (m + n)) (j : Fin n) :
    (g * lower m n R Y) i (j.natAdd m) = g i (j.natAdd m) := by
  rw [mul_apply_split]
  simp

/-- Left multiplication by `lower(Y)` keeps the rows of the first block. -/
theorem lower_mul_apply_castAdd (g : Langlands.GeneralLinear (m + n) R)
    (Y : Matrix (Fin n) (Fin m) R) (i : Fin m) (j : Fin (m + n)) :
    (lower m n R Y * g) (i.castAdd n) j = g (i.castAdd n) j := by
  rw [mul_apply_split]
  simp

/-- `lower(Y)` is lower unitriangular, so its determinant is one. -/
theorem det_lower (Y : Matrix (Fin n) (Fin m) R) :
    (lower m n R Y).val.det = 1 := by
  have hlt : (lower m n R Y).val.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        have hne : i ≠ j := by
          rintro rfl
          exact lt_irrefl _ hij
        change lower m n R Y (i.castAdd n) (j.castAdd n) = 0
        simp [hne]
      | right j =>
        simp
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        exact absurd hij (not_lt.2 (le_of_lt (castAdd_lt_natAdd j i)))
      | right j =>
        have hne : i ≠ j := by
          rintro rfl
          exact lt_irrefl _ hij
        change lower m n R Y (i.natAdd m) (j.natAdd m) = 0
        simp [hne]
  rw [Matrix.det_of_isLowerTriangular _ hlt, Fin.prod_univ_add]
  simp

end Lower

section Valued

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation F Γ₀} {m n : ℕ}

/-- The diagonal entries of the inverse of an upper triangular matrix are the inverses of
its diagonal entries. -/
theorem inv_apply_self_mul {k : ℕ} (b : Matrix.GeneralLinearGroup (Fin k) F)
    (hb : b.val.IsUpperTriangular) (i : Fin k) : b⁻¹ i i * b i i = 1 := by
  have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin k) F =>
    (g : Matrix (Fin k) (Fin k) F) i i) (inv_mul_cancel b)
  simp only [Units.val_mul, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Iwasawa.upperTriangular_mul_apply_self (inv_isUpperTriangular b hb) hb] at h

variable {Y : Matrix (Fin n) (Fin m) F} {b k : Langlands.GeneralLinear (m + n) F}

/-- In `lower(Y) = b k`, the first diagonal block of `b` has the entries of `k⁻¹`. -/
theorem topLeft_apply_of_lower_eq (hb : b.val.IsUpperTriangular) (h : lower m n F Y = b * k)
    (i j : Fin m) : topLeft b hb i j = k⁻¹ (i.castAdd n) (j.castAdd n) := by
  have hb' : b = lower m n F Y * k⁻¹ := by rw [h, mul_inv_cancel_right]
  rw [topLeft_apply, hb', lower_mul_apply_castAdd]

/-- In `lower(Y) = b k`, the inverse of the second diagonal block of `b` has the entries
of `k`. -/
theorem botRight_inv_apply_of_lower_eq (hb : b.val.IsUpperTriangular)
    (h : lower m n F Y = b * k) (i j : Fin n) :
    (botRight b hb)⁻¹ i j = k (i.natAdd m) (j.natAdd m) := by
  have hb' : b⁻¹ = k * lower m n F (-Y) := by
    rw [← lower_inv, h, _root_.mul_inv_rev, mul_inv_cancel_left]
  rw [botRight_inv_apply, hb', mul_lower_apply_natAdd]

/-- In `lower(Y) = b k`, the matrix `b₂₂⁻¹ Y` has the entries of the lower left block of
`k`. -/
theorem botRight_inv_mul_apply_of_lower_eq (hb : b.val.IsUpperTriangular)
    (h : lower m n F Y = b * k) (i : Fin n) (j : Fin m) :
    ∑ l : Fin n, (botRight b hb)⁻¹ i l * Y l j = k (i.natAdd m) (j.castAdd n) := by
  have hk : k = b⁻¹ * lower m n F Y := by rw [h, inv_mul_cancel_left]
  rw [hk, mul_apply_split]
  simp only [botRight_inv_apply, lowerLeft_eq_zero (inv_isUpperTriangular b hb), zero_mul,
    Finset.sum_const_zero, zero_add, lower_second_first]

end Valued

section Torus

variable {F : Type*} [Field F] {m n : ℕ}

open Iwasawa

theorem isUpperTriangular_mul_torus {u : Langlands.GeneralLinear (m + n) F}
    (hu : u ∈ upperUnipotent (m + n) F) (ϖ : Fˣ) (ν : Fin (m + n) → ℤ) :
    (u * torus ϖ ν).val.IsUpperTriangular := by
  rw [Units.val_mul, torus_val]
  exact hu.1.mul (Matrix.blockTriangular_diagonal _)

theorem mul_torus_apply (u : Langlands.GeneralLinear (m + n) F) (ϖ : Fˣ)
    (ν : Fin (m + n) → ℤ) (i j : Fin (m + n)) :
    (u * torus ϖ ν) i j = u i j * ((ϖ ^ ν j : Fˣ) : F) := by
  change (u.val * (torus ϖ ν).val) i j = _
  rw [torus_val, Matrix.mul_diagonal]

theorem mul_torus_apply_self {u : Langlands.GeneralLinear (m + n) F}
    (hu : u ∈ upperUnipotent (m + n) F) (ϖ : Fˣ) (ν : Fin (m + n) → ℤ) (i : Fin (m + n)) :
    (u * torus ϖ ν) i i = ((ϖ ^ ν i : Fˣ) : F) := by
  rw [mul_torus_apply, hu.2 i, one_mul]

theorem topLeft_mem_upperUnipotent {u : Langlands.GeneralLinear (m + n) F}
    (hu : u ∈ upperUnipotent (m + n) F) :
    topLeft u hu.1 ∈ upperUnipotent m F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · exact hu.1 (show (j.castAdd n : Fin (m + n)) < i.castAdd n from hij)
  · exact hu.2 (i.castAdd n)

theorem botRight_mem_upperUnipotent {u : Langlands.GeneralLinear (m + n) F}
    (hu : u ∈ upperUnipotent (m + n) F) :
    botRight u hu.1 ∈ upperUnipotent n F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hji : (j : ℕ) < i := hij
    exact hu.1 (show (j.natAdd m : Fin (m + n)) < i.natAdd m by
      rw [Fin.lt_def]
      simp only [Fin.val_natAdd]
      omega)
  · exact hu.2 (i.natAdd m)

theorem topLeft_mul_torus {u : Langlands.GeneralLinear (m + n) F}
    (hu : u ∈ upperUnipotent (m + n) F) (ϖ : Fˣ) (ν : Fin (m + n) → ℤ) :
    topLeft (u * torus ϖ ν) (isUpperTriangular_mul_torus hu ϖ ν) =
      topLeft u hu.1 * torus ϖ (fun i => ν (i.castAdd n)) := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, torus_val, Matrix.mul_diagonal]
  exact mul_torus_apply u ϖ ν _ _

theorem botRight_mul_torus {u : Langlands.GeneralLinear (m + n) F}
    (hu : u ∈ upperUnipotent (m + n) F) (ϖ : Fˣ) (ν : Fin (m + n) → ℤ) :
    botRight (u * torus ϖ ν) (isUpperTriangular_mul_torus hu ϖ ν) =
      botRight u hu.1 * torus ϖ (fun i => ν (i.natAdd m)) := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, torus_val, Matrix.mul_diagonal]
  exact mul_torus_apply u ϖ ν _ _

end Torus

section Exponent

open Langlands.Conductor

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation F Γ₀} {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement v ϖ) {r t : ℕ}

open Iwasawa

include hϖ in
theorem valuation_zpow_le_one_iff (k : ℤ) : v (((ϖ ^ k : Fˣ) : F)) ≤ 1 ↔ 0 ≤ k := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  have h := (zpow_right_strictAnti₀ (valuation_pos v ϖ) hϖ.1).le_iff_ge (a := k) (b := 0)
  simpa using h

include hϖ in
theorem valuation_zpow_eq_one_iff (k : ℤ) : v (((ϖ ^ k : Fˣ) : F)) = 1 ↔ k = 0 := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  constructor
  · intro h
    exact (zpow_right_strictAnti₀ (valuation_pos v ϖ) hϖ.1).injective (by simpa using h)
  · rintro rfl
    simp

/-- The determinant of a matrix with integral entries is integral. -/
theorem det_mem_integer {k : ℕ} (M : Matrix (Fin k) (Fin k) F) (hM : ∀ a b, M a b ∈ v.integer) :
    M.det ∈ v.integer := by
  let M' : Matrix (Fin k) (Fin k) v.integer := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hM' : v.integer.subtype.mapMatrix M' = M := by
    ext a b
    rfl
  rw [← hM', ← RingHom.map_det]
  exact (M'.det).property

/-- The adjugate of a matrix with integral entries is integral. -/
theorem adjugate_mem_integer {k : ℕ} (M : Matrix (Fin k) (Fin k) F)
    (hM : ∀ a b, M a b ∈ v.integer) (a b : Fin k) : M.adjugate a b ∈ v.integer := by
  let M' : Matrix (Fin k) (Fin k) v.integer := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hM' : v.integer.subtype.mapMatrix M' = M := by
    ext a b
    rfl
  rw [← hM', ← RingHom.map_adjugate]
  exact (M'.adjugate a b).property

/-- An integral matrix with integral inverse has a determinant of valuation one. -/
theorem valuation_det_eq_one {k : ℕ} {g : Matrix.GeneralLinearGroup (Fin (k + 1)) F}
    (hg : g ∈ integralSubgroup v.integer k) : v (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det = 1 := by
  rw [mem_integralSubgroup v.integer k g] at hg
  have h1 := (Valuation.mem_integer_iff v _).1 (det_mem_integer _ hg.1)
  have h2 := (Valuation.mem_integer_iff v _).1 (det_mem_integer _ hg.2)
  have hprod : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det
        = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h3 := congrArg v hprod
  rw [map_mul, map_one] at h3
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
  rw [h3] at this
  exact lt_irrefl _ this

/-- The Iwasawa exponent of `lower(Y)` in `GL_((r+1)+(t+1))`. -/
def openCellExponent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F) : Fin ((r + 1) + (t + 1)) → ℤ :=
  exponent (n := r + 1 + t) hϖ (lower (r + 1) (t + 1) F Y)

theorem exists_eq_openCellExponent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F) :
    ∃ u ∈ upperUnipotent ((r + 1) + (t + 1)) F, ∃ k ∈ integralSubgroup v.integer (r + 1 + t),
      lower (r + 1) (t + 1) F Y = u * torus ϖ (openCellExponent hϖ Y) * k :=
  exists_eq_exponent (n := r + 1 + t) hϖ (lower (r + 1) (t + 1) F Y)

/-- The exponents of the first block are nonnegative: the first Levi factor is integral. -/
theorem openCellExponent_castAdd_nonneg (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F)
    (i : Fin (r + 1)) : 0 ≤ openCellExponent hϖ Y (i.castAdd (t + 1)) := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_openCellExponent hϖ Y
  have hb := isUpperTriangular_mul_torus hu ϖ (openCellExponent hϖ Y)
  have h1 := topLeft_apply_of_lower_eq hb h i i
  rw [topLeft_apply, mul_torus_apply_self hu] at h1
  have h2 := ((mem_integralSubgroup v.integer (r + 1 + t) k).1 hk).2
    (i.castAdd (t + 1)) (i.castAdd (t + 1))
  rw [← h1, Valuation.mem_integer_iff, valuation_zpow_le_one_iff hϖ] at h2
  exact h2

/-- The exponents of the second block are nonpositive: the inverse of the second Levi factor
is integral. -/
theorem openCellExponent_natAdd_nonpos (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F)
    (j : Fin (t + 1)) : openCellExponent hϖ Y (j.natAdd (r + 1)) ≤ 0 := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_openCellExponent hϖ Y
  have hb := isUpperTriangular_mul_torus hu ϖ (openCellExponent hϖ Y)
  have h1 := botRight_inv_apply_of_lower_eq hb h j j
  have h3 := inv_apply_self_mul _ hb (j.natAdd (r + 1))
  rw [botRight_inv_apply] at h1
  rw [mul_torus_apply_self hu, h1, ← eq_mul_inv_iff_mul_eq₀
    (Units.ne_zero _), one_mul, ← Units.val_inv_eq_inv_val, ← zpow_neg] at h3
  have h2 := ((mem_integralSubgroup v.integer (r + 1 + t) k).1 hk).1
    (j.natAdd (r + 1)) (j.natAdd (r + 1))
  rw [h3, Valuation.mem_integer_iff, valuation_zpow_le_one_iff hϖ] at h2
  omega

theorem zpow_finset_sum {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

/-- The Iwasawa exponent of `lower(Y)` has total sum zero, since `det lower(Y) = 1`. -/
theorem sum_openCellExponent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F) :
    ∑ i, openCellExponent hϖ Y i = 0 := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_openCellExponent hϖ Y
  have hdet := congrArg (fun g : Langlands.GeneralLinear ((r + 1) + (t + 1)) F => g.val.det) h
  simp only [det_lower, Units.val_mul, Matrix.det_mul] at hdet
  have hu1 : u.val.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hu.1]
    exact Finset.prod_eq_one fun i _ => hu.2 i
  rw [hu1, one_mul, torus_val, Matrix.det_diagonal] at hdet
  have hv := congrArg v hdet
  rw [map_one, map_mul, valuation_det_eq_one hk, mul_one, ← Units.coe_prod,
    ← zpow_finset_sum] at hv
  exact (valuation_zpow_eq_one_iff hϖ _).1 hv.symm

/-- The depth `D = ∑ λ_i` of `Y`: the sum of the exponents of the first block. -/
def openCellDepth (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F) : ℤ :=
  ∑ i : Fin (r + 1), openCellExponent hϖ Y (i.castAdd (t + 1))

theorem openCellDepth_nonneg (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F) :
    0 ≤ openCellDepth hϖ Y :=
  Finset.sum_nonneg fun i _ => openCellExponent_castAdd_nonneg hϖ Y i

theorem sum_openCellExponent_natAdd (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F) :
    ∑ j : Fin (t + 1), openCellExponent hϖ Y (j.natAdd (r + 1)) = -openCellDepth hϖ Y := by
  have h := sum_openCellExponent hϖ Y
  rw [Fin.sum_univ_add] at h
  rw [openCellDepth]
  linarith

/-- An invertible matrix is its determinant times the adjugate of its inverse. -/
theorem val_eq_det_smul_adjugate_inv {k : ℕ} (A : Langlands.GeneralLinear k F) :
    (A : Matrix (Fin k) (Fin k) F) =
      (A : Matrix (Fin k) (Fin k) F).det •
        ((A⁻¹ : Langlands.GeneralLinear k F) : Matrix (Fin k) (Fin k) F).adjugate := by
  have h1 : ((A⁻¹ : Langlands.GeneralLinear k F) : Matrix (Fin k) (Fin k) F) *
      ((A : Matrix (Fin k) (Fin k) F).det •
        ((A⁻¹ : Langlands.GeneralLinear k F) : Matrix (Fin k) (Fin k) F).adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one, one_smul]
  calc
    (A : Matrix (Fin k) (Fin k) F) =
        (A : Matrix (Fin k) (Fin k) F) * (((A⁻¹ : Langlands.GeneralLinear k F) :
          Matrix (Fin k) (Fin k) F) * ((A : Matrix (Fin k) (Fin k) F).det •
            ((A⁻¹ : Langlands.GeneralLinear k F) : Matrix (Fin k) (Fin k) F).adjugate)) := by
      rw [h1, Matrix.mul_one]
    _ = _ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

/-- `ϖ ^ D • Y` is integral, `D` the depth. -/
theorem uniformizer_pow_depth_mul_mem (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) F)
    (i : Fin (t + 1)) (j : Fin (r + 1)) :
    ((ϖ ^ openCellDepth hϖ Y : Fˣ) : F) * Y i j ∈ v.integer := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_openCellExponent hϖ Y
  have hb := isUpperTriangular_mul_torus hu ϖ (openCellExponent hϖ Y)
  set b := u * torus ϖ (openCellExponent hϖ Y) with hbdef
  set B := botRight b hb with hB
  have hk' := (mem_integralSubgroup v.integer (r + 1 + t) k).1 hk
  -- `B⁻¹ Y` is integral
  have hBY : ∀ a c, ((B⁻¹ : Langlands.GeneralLinear (t + 1) F).val * Y) a c ∈ v.integer := by
    intro a c
    rw [Matrix.mul_apply, botRight_inv_mul_apply_of_lower_eq hb h]
    exact hk'.1 _ _
  have hBinv : ∀ a c, (B⁻¹ : Langlands.GeneralLinear (t + 1) F) a c ∈ v.integer := by
    intro a c
    rw [hB, botRight_inv_apply_of_lower_eq hb h]
    exact hk'.1 _ _
  -- `det B = ϖ ^ (-D)`
  have hBtri : (B : Matrix (Fin (t + 1)) (Fin (t + 1)) F).IsUpperTriangular := by
    intro a c hac
    exact hb (show (c.natAdd (r + 1) : Fin ((r + 1) + (t + 1))) < a.natAdd (r + 1) by
      have : (c : ℕ) < a := hac
      rw [Fin.lt_def]
      simp only [Fin.val_natAdd]
      omega)
  have hdetB : (B : Matrix (Fin (t + 1)) (Fin (t + 1)) F).det =
      ((ϖ ^ (-openCellDepth hϖ Y) : Fˣ) : F) := by
    rw [Matrix.det_of_isUpperTriangular hBtri, ← sum_openCellExponent_natAdd, zpow_finset_sum,
      Units.coe_prod]
    exact Finset.prod_congr rfl fun a _ => mul_torus_apply_self hu ϖ _ _
  have hYeq : Y = (B : Matrix (Fin (t + 1)) (Fin (t + 1)) F) *
      ((B⁻¹ : Langlands.GeneralLinear (t + 1) F).val * Y) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have key : ((ϖ ^ openCellDepth hϖ Y : Fˣ) : F) * Y i j =
      (((B⁻¹ : Langlands.GeneralLinear (t + 1) F).val.adjugate) *
        ((B⁻¹ : Langlands.GeneralLinear (t + 1) F).val * Y)) i j := by
    have hYij : Y i j = ((ϖ ^ (-openCellDepth hϖ Y) : Fˣ) : F) *
        (((B⁻¹ : Langlands.GeneralLinear (t + 1) F).val.adjugate) *
          ((B⁻¹ : Langlands.GeneralLinear (t + 1) F).val * Y)) i j := by
      conv_lhs => rw [hYeq, val_eq_det_smul_adjugate_inv B, hdetB, Matrix.smul_mul,
        Matrix.smul_apply, smul_eq_mul]
    rw [hYij, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, one_mul]
  rw [key, Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ =>
    mul_mem (adjugate_mem_integer _ hBinv _ _) (hBY _ _)

end Exponent

end Langlands.Shahidi.OpenCell
