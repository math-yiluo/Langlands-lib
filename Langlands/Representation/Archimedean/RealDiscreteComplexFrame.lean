import Langlands.Representation.Archimedean.RealDiscreteFrame

/-!
# The complex frame adapted to a block layout

Fix `a ≤ n` with `n - a` even. The coordinates `l < a` are character coordinates, and the
coordinates `a + 2r`, `a + 2r + 1` form the planes of the induction blocks. The frame matrix `U`
is the identity on the character coordinates and has the columns `e_p + i e_{p+1}` and
`e_p - i e_{p+1}` on the plane `p, p + 1`. This module proves the four identities the scalar
step uses:

* `U V = 1` for an explicit `V`;
* the rotation `r_p(θ)` of a plane acts by `U ↦ U diag(e^{-iθ}, e^{iθ})` on that plane;
* a sign matrix that is constant on every plane commutes with `U`;
* the sign `-1` at the second coordinate `p + 1` of a plane swaps the two columns of the plane.
-/

noncomputable section

open Matrix Finset

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

namespace RealDiscreteFrame

open RealDiscreteScalar PrincipalSeriesExtension GramFormula RealBlockRotation

variable {n : ℕ}

/-! ## Two matrix-product formulas -/

theorem mul_apply_eq_single (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n)
    (hB : ∀ j, j ≠ k → B j k = 0) : (A * B) i k = A i k * B k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k (fun j _ hj => by rw [hB j hj, mul_zero])
    (fun h => absurd (mem_univ k) h)]

theorem mul_apply_eq_pair (A B : Matrix (Fin n) (Fin n) ℂ) (i k k' : Fin n) (hk : k ≠ k')
    (hB : ∀ j, j ≠ k → j ≠ k' → B j k = 0) :
    (A * B) i k = A i k * B k k + A i k' * B k' k := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem k k' (mem_univ _) (mem_univ _) hk
    (fun j _ hj => by rw [hB j hj.1 hj.2, mul_zero])]

/-! ## The frame and its inverse -/

/-- The complex frame: the identity on the coordinates `l < a`, and the columns
`e_p + i e_{p+1}` (column `p`) and `e_p - i e_{p+1}` (column `p + 1`) on every plane
`p = a + 2r`. -/
def frameU (n a : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if (j : ℕ) < a then (if (i : ℕ) = j then 1 else 0)
    else if ((j : ℕ) - a) % 2 = 0 then
      (if (i : ℕ) = j then 1 else if (i : ℕ) = j + 1 then Complex.I else 0)
    else (if (i : ℕ) = j then -Complex.I else if (i : ℕ) + 1 = j then 1 else 0)

/-- The inverse frame: on every plane it is `(1/2) [[1, -i], [1, i]]`. -/
def frameV (n a : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if (j : ℕ) < a then (if (i : ℕ) = j then 1 else 0)
    else if ((j : ℕ) - a) % 2 = 0 then
      (if (i : ℕ) = j then 1 / 2 else if (i : ℕ) = j + 1 then 1 / 2 else 0)
    else (if (i : ℕ) = j then Complex.I / 2 else if (i : ℕ) + 1 = j then -Complex.I / 2 else 0)

theorem frameU_apply (a : ℕ) (i j : Fin n) :
    frameU n a i j =
      if (j : ℕ) < a then (if (i : ℕ) = j then 1 else 0)
      else if ((j : ℕ) - a) % 2 = 0 then
        (if (i : ℕ) = j then 1 else if (i : ℕ) = j + 1 then Complex.I else 0)
      else (if (i : ℕ) = j then -Complex.I else if (i : ℕ) + 1 = j then 1 else 0) :=
  rfl

theorem frameV_apply (a : ℕ) (i j : Fin n) :
    frameV n a i j =
      if (j : ℕ) < a then (if (i : ℕ) = j then 1 else 0)
      else if ((j : ℕ) - a) % 2 = 0 then
        (if (i : ℕ) = j then 1 / 2 else if (i : ℕ) = j + 1 then 1 / 2 else 0)
      else (if (i : ℕ) = j then Complex.I / 2 else if (i : ℕ) + 1 = j then -Complex.I / 2 else 0) :=
  rfl

theorem frameU_char_col (a : ℕ) {k : Fin n} (hk : (k : ℕ) < a) (i : Fin n) :
    frameU n a i k = if (i : ℕ) = k then 1 else 0 := by
  rw [frameU_apply, ite_eq_left hk]

theorem frameU_z_col {a : ℕ} {k : Fin n} (hk : a ≤ (k : ℕ)) (he : ((k : ℕ) - a) % 2 = 0)
    (i : Fin n) :
    frameU n a i k = if (i : ℕ) = k then 1 else if (i : ℕ) = k + 1 then Complex.I else 0 := by
  rw [frameU_apply, ite_eq_right (by omega), ite_eq_left he]

theorem frameU_zbar_col {a : ℕ} {k : Fin n} (hk : a ≤ (k : ℕ)) (he : ((k : ℕ) - a) % 2 = 1)
    (i : Fin n) :
    frameU n a i k = if (i : ℕ) = k then -Complex.I else if (i : ℕ) + 1 = k then 1 else 0 := by
  rw [frameU_apply, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The partner of a coordinate: itself for `l < a`, and the other coordinate of its plane. -/
theorem exists_partner {a : ℕ} (hev : (n - a) % 2 = 0) (k : Fin n)
    (hk : a ≤ (k : ℕ)) :
    ∃ k' : Fin n, k ≠ k' ∧
      (((k : ℕ) - a) % 2 = 0 → (k' : ℕ) = k + 1) ∧ (((k : ℕ) - a) % 2 = 1 → (k' : ℕ) + 1 = k) := by
  by_cases he : ((k : ℕ) - a) % 2 = 0
  · refine ⟨⟨k + 1, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h, fun _ => rfl,
      fun h => by omega⟩
  · refine ⟨⟨k - 1, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega,
      fun h => by omega, fun _ => by simp; omega⟩

/-- The column `k` of `frameU` or `frameV` vanishes outside `k` and its partner. -/
theorem frameV_col (a : ℕ) {k k' : Fin n} (hk : a ≤ (k : ℕ))
    (h0 : ((k : ℕ) - a) % 2 = 0 → (k' : ℕ) = k + 1) (h1 : ((k : ℕ) - a) % 2 = 1 → (k' : ℕ) + 1 = k)
    (j : Fin n) (hj : j ≠ k) (hj' : j ≠ k') : frameV n a j k = 0 ∧ frameU n a j k = 0 := by
  rw [Ne, Fin.ext_iff] at hj hj'
  rw [frameV_apply, frameU_apply]
  constructor <;> split_ifs <;> first | rfl | omega

theorem frameV_col_char (a : ℕ) {k : Fin n} (hk : (k : ℕ) < a) (j : Fin n) (hj : j ≠ k) :
    frameV n a j k = 0 ∧ frameU n a j k = 0 := by
  rw [Ne, Fin.ext_iff] at hj
  rw [frameV_apply, frameU_apply]
  constructor <;> split_ifs <;> rfl

/-- **The frame is invertible.** -/
theorem frameU_mul_frameV {a : ℕ} (hev : (n - a) % 2 = 0) :
    frameU n a * frameV n a = 1 := by
  ext i k
  rw [Matrix.one_apply]
  by_cases hk : (k : ℕ) < a
  · rw [mul_apply_eq_single _ _ i k fun j hj => (frameV_col_char a hk j hj).1, frameU_apply,
      frameV_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> simp
  · obtain ⟨k', hkk', h0, h1⟩ := exists_partner hev k (by omega)
    rw [mul_apply_eq_pair _ _ i k k' hkk' fun j hj hj' =>
      (frameV_col a (by omega) h0 h1 j hj hj').1, frameU_apply, frameU_apply, frameV_apply,
      frameV_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)

/-! ## Rotations -/

/-- The rotation weight of a coordinate for the plane `p, p + 1`: `-1` at `p`, `1` at `p + 1`. -/
def rotC (p : ℕ) (l : Fin n) : ℤ :=
  if (l : ℕ) = p then -1 else if (l : ℕ) = p + 1 then 1 else 0

theorem exp_rot_neg (θ : ℝ) :
    Complex.exp (((-1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [show ((-1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem exp_rot_pos (θ : ℝ) :
    Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [show ((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I = ((θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem exp_rot_zero (θ : ℝ) : Complex.exp (((0 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) = 1 := by
  simp

theorem kmat_rot_apply {p : ℕ} (hp : p + 1 < n) (θ : ℝ) (i j : Fin n) :
    kmat (rot n p θ) i j =
      ((if (i : ℕ) = p + 1 ∧ (j : ℕ) = p then Real.sin θ
        else if (i : ℕ) = p ∧ (j : ℕ) = p + 1 then -Real.sin θ
        else if (i : ℕ) = j ∧ ((i : ℕ) = p ∨ (i : ℕ) = p + 1) then Real.cos θ
        else if (i : ℕ) = j then 1 else 0 : ℝ) : ℂ) := by
  unfold kmat
  rw [Matrix.map_apply]
  change ((blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ) i j : ℂ) = _
  rw [blockRotation_apply hp]
  simp only [Fin.ext_iff]

theorem exp_rotC (p : ℕ) (θ : ℝ) (l : Fin n) :
    Complex.exp ((rotC p l : ℂ) * (θ : ℂ) * Complex.I) =
      if (l : ℕ) = p then (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I
      else if (l : ℕ) = p + 1 then (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I else 1 := by
  unfold rotC
  split_ifs
  · exact exp_rot_neg θ
  · exact exp_rot_pos θ
  · exact exp_rot_zero θ

theorem rot_col_char {a p : ℕ} (hap : a ≤ p) (hp : p + 1 < n) (θ : ℝ) (i : Fin n) {k : Fin n}
    (hk : (k : ℕ) < a) :
    (kmat (rot n p θ) * frameU n a) i k =
      frameU n a i k * Complex.exp ((rotC p k : ℂ) * (θ : ℂ) * Complex.I) := by
  rw [exp_rotC, mul_apply_eq_single _ _ i k fun j hj => (frameV_col_char a hk j hj).2,
    kmat_rot_apply hp, frameU_char_col a hk, frameU_char_col a hk, ite_eq_left rfl,
    ite_eq_right (by omega), ite_eq_right (by omega)]
  split_ifs <;> (try simp only [Complex.ofReal_one, Complex.ofReal_zero]) <;> omega

theorem rot_col_z {a p : ℕ} (hap : a ≤ p) (hpe : (p - a) % 2 = 0) (hp : p + 1 < n) (θ : ℝ) (i : Fin n)
    {k k' : Fin n} (hk : a ≤ (k : ℕ)) (he : ((k : ℕ) - a) % 2 = 0) (hkk' : k ≠ k')
    (hk' : (k' : ℕ) = k + 1) :
    (kmat (rot n p θ) * frameU n a) i k =
      frameU n a i k * Complex.exp ((rotC p k : ℂ) * (θ : ℂ) * Complex.I) := by
  rw [exp_rotC, mul_apply_eq_pair _ _ i k k' hkk' fun j hj hj' =>
    (frameV_col a hk (fun _ => hk') (fun h => by omega) j hj hj').2, kmat_rot_apply hp,
    kmat_rot_apply hp]
  have hkk : frameU n a k k = 1 := by rw [frameU_z_col hk he, ite_eq_left rfl]
  have hk'k : frameU n a k' k = Complex.I := by
    rw [frameU_z_col hk he, ite_eq_right (by omega), ite_eq_left hk']
  rw [hkk, hk'k, frameU_z_col hk he i]
  by_cases hkp : (k : ℕ) = p
  · rw [ite_eq_left hkp]
    split_ifs <;>
      (try simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero]) <;>
      first
      | (exfalso; omega)
      | ring1
      | (ring_nf; rw [Complex.I_sq]; ring1)
  · rw [ite_eq_right hkp, ite_eq_right (by omega)]
    split_ifs <;>
      (try simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero]) <;>
      first
      | (exfalso; omega)
      | ring1

theorem rot_col_zbar {a p : ℕ} (hap : a ≤ p) (hpe : (p - a) % 2 = 0) (hp : p + 1 < n) (θ : ℝ) (i : Fin n)
    {k k' : Fin n} (hk : a ≤ (k : ℕ)) (he : ((k : ℕ) - a) % 2 = 1) (hkk' : k ≠ k')
    (hk' : (k' : ℕ) + 1 = k) :
    (kmat (rot n p θ) * frameU n a) i k =
      frameU n a i k * Complex.exp ((rotC p k : ℂ) * (θ : ℂ) * Complex.I) := by
  rw [exp_rotC, mul_apply_eq_pair _ _ i k k' hkk' fun j hj hj' =>
    (frameV_col a hk (fun h => by omega) (fun _ => hk') j hj hj').2, kmat_rot_apply hp,
    kmat_rot_apply hp]
  have hkk : frameU n a k k = -Complex.I := by rw [frameU_zbar_col hk he, ite_eq_left rfl]
  have hk'k : frameU n a k' k = 1 := by
    rw [frameU_zbar_col hk he, ite_eq_right (by omega), ite_eq_left hk']
  rw [hkk, hk'k, frameU_zbar_col hk he i]
  by_cases hkp : (k : ℕ) = p + 1
  · rw [ite_eq_right (by omega), ite_eq_left hkp]
    split_ifs <;>
      (try simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero]) <;>
      first
      | (exfalso; omega)
      | ring1
      | (ring_nf; rw [Complex.I_sq]; ring1)
  · rw [ite_eq_right (by omega), ite_eq_right hkp]
    split_ifs <;>
      (try simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero]) <;>
      first
      | (exfalso; omega)
      | ring1

/-- **Rotation eigen-relation.** For a plane `p = a + 2r`,
`r_p(θ) U = U diag(e^{i c_l θ})` with `c = rotC p`. -/
theorem kmat_rot_mul_frameU {a p : ℕ} (hev : (n - a) % 2 = 0) (hap : a ≤ p)
    (hpe : (p - a) % 2 = 0) (hp : p + 1 < n) (θ : ℝ) :
    kmat (rot n p θ) * frameU n a =
      frameU n a * Matrix.diagonal fun l => Complex.exp ((rotC p l : ℂ) * (θ : ℂ) * Complex.I) := by
  ext i k
  rw [Matrix.mul_diagonal]
  by_cases hk : (k : ℕ) < a
  · exact rot_col_char hap hp θ i hk
  · obtain ⟨k', hkk', h0, h1⟩ := exists_partner hev k (by omega)
    by_cases he : ((k : ℕ) - a) % 2 = 0
    · exact rot_col_z hap hpe hp θ i (by omega) he hkk' (h0 he)
    · exact rot_col_zbar hap hpe hp θ i (by omega) (by omega) hkk' (h1 (by omega))

/-! ## Sign matrices -/

theorem kmat_signDiagonal (d : Fin n → ℝ) :
    kmat (signDiagonal d) = Matrix.diagonal fun l => ((signReal (d l) : ℝ) : ℂ) := by
  ext i j
  unfold kmat signDiagonal
  rw [Matrix.map_apply]
  change ((Matrix.diagonal fun l => signReal (d l)) i j : ℂ) = _
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem toUnits_signDiagonal (s : Fin n → ℝˣ) :
    Unitary.toUnits (signDiagonal fun i => (s i : ℝ)) =
      (Iwasawa.diagonalUnits fun i => signUnit (s i) : Langlands.GeneralLinear n ℝ) :=
  Langlands.Archimedean.InductionStages.toUnits_signDiagonal s

/-- A diagonal matrix that is constant on every plane commutes with the frame. -/
theorem diagonal_mul_frameU {a : ℕ} (μ : Fin n → ℂ)
    (hμ : ∀ i j : Fin n, a ≤ (j : ℕ) →
      ((((j : ℕ) - a) % 2 = 0 ∧ (i : ℕ) = j + 1) ∨ (((j : ℕ) - a) % 2 = 1 ∧ (i : ℕ) + 1 = j)) →
        μ i = μ j) :
    Matrix.diagonal μ * frameU n a = frameU n a * Matrix.diagonal μ := by
  ext i k
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, frameU_apply]
  by_cases hik : (i : ℕ) = k
  · rw [Fin.ext hik]
    ring
  · split_ifs <;> first
      | (rw [hμ i k (by omega) (Or.inl ⟨by omega, by omega⟩)]; ring1)
      | (rw [hμ i k (by omega) (Or.inr ⟨by omega, by omega⟩)]; ring1)
      | ring1

/-- The sign `-1` at the second coordinate `p + 1` of a plane swaps the two columns of the
plane. -/
theorem diagonal_flip_mul_frameU {a p : ℕ} (hap : a ≤ p) (hpe : (p - a) % 2 = 0)
    (hp : p + 1 < n) :
    Matrix.diagonal (fun l : Fin n => if (l : ℕ) = p + 1 then (-1 : ℂ) else 1) * frameU n a =
      (frameU n a).submatrix id
        (Equiv.swap (⟨p, by omega⟩ : Fin n) (⟨p + 1, hp⟩ : Fin n)) := by
  ext i k
  simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, id]
  by_cases hkp : k = ⟨p, by omega⟩
  · rw [hkp, Equiv.swap_apply_left,
      frameU_z_col (k := ⟨p, by omega⟩) (by simp; omega) (by simpa using hpe),
      frameU_zbar_col (k := ⟨p + 1, hp⟩) (by simp; omega) (by simp; omega)]
    simp only
    split_ifs <;> first | (exfalso; omega) | ring1
  · by_cases hkq : k = ⟨p + 1, hp⟩
    · rw [hkq, Equiv.swap_apply_right,
        frameU_z_col (k := ⟨p, by omega⟩) (by simp; omega) (by simpa using hpe),
        frameU_zbar_col (k := ⟨p + 1, hp⟩) (by simp; omega) (by simp; omega)]
      simp only
      split_ifs <;> first | (exfalso; omega) | ring1
    · rw [Equiv.swap_apply_of_ne_of_ne hkp hkq, frameU_apply]
      have h1 : (k : ℕ) ≠ p := fun h => hkp (Fin.ext h)
      have h2 : (k : ℕ) ≠ p + 1 := fun h => hkq (Fin.ext h)
      split_ifs <;> first | (exfalso; omega) | ring1

end RealDiscreteFrame

end Langlands.Archimedean
