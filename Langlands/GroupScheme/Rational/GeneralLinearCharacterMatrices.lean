import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Pi.Units

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- An invertible diagonal matrix with its diagonal specified by units. -/
def diagonalMatrixUnits (R : Type v) [CommRing R] : (n → Rˣ) →* GL n R :=
  (Units.map (Matrix.diagonalRingHom n R).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

@[simp] theorem diagonalMatrixUnits_val {R : Type v} [CommRing R] (d : n → Rˣ) :
    (diagonalMatrixUnits R d : Matrix n n R) = Matrix.diagonal (fun i => (d i : R)) := rfl

/-- The diagonal embedding which changes only the `i`-th diagonal entry. -/
def coordinateDiagonalUnits (R : Type v) [CommRing R] (i : n) : Rˣ →* GL n R :=
  (diagonalMatrixUnits R).comp (MonoidHom.mulSingle (fun _ : n => Rˣ) i)

@[simp] theorem coordinateDiagonalUnits_apply {R : Type v} [CommRing R]
    (i : n) (a : Rˣ) :
    coordinateDiagonalUnits R i a = diagonalMatrixUnits R (Pi.mulSingle i a) := rfl

section Field

variable {F : Type v} [Field F] {C : Type w} [CommGroup C]

private def permutationMatrixUnit (σ : Equiv.Perm n) : GL n F where
  val := (1 : Matrix n n F).submatrix σ id
  inv := (1 : Matrix n n F).submatrix σ.symm id
  val_inv := by simp
  inv_val := by simp

private theorem character_eq_of_intertwine (χ : GL n F →* C)
    (g h p : GL n F) (hp : p * g = h * p) : χ g = χ h := by
  apply mul_left_cancel (a := χ p)
  simpa only [map_mul, mul_comm (χ h)] using congrArg χ hp

private theorem character_diagonal_permute (χ : GL n F →* C)
    (d : n → Fˣ) (σ : Equiv.Perm n) :
    χ (diagonalMatrixUnits F d) = χ (diagonalMatrixUnits F (d ∘ σ)) := by
  apply character_eq_of_intertwine χ _ _ (permutationMatrixUnit σ)
  apply Units.ext
  change (1 : Matrix n n F).submatrix σ id * diagonal (fun i => (d i : F)) =
    diagonal (fun i => (d (σ i) : F)) * (1 : Matrix n n F).submatrix σ id
  ext i j
  simp [mul_diagonal, diagonal_mul, submatrix, one_apply]
  split_ifs with h
  · simp [h]
  · simp

theorem character_coordinateDiagonal_eq (χ : GL n F →* C)
    (i j : n) (a : Fˣ) :
    χ (coordinateDiagonalUnits F j a) = χ (coordinateDiagonalUnits F i a) := by
  change χ (diagonalMatrixUnits F (Pi.mulSingle j a)) =
    χ (diagonalMatrixUnits F (Pi.mulSingle i a))
  convert character_diagonal_permute χ (Pi.mulSingle j a) (Equiv.swap i j) using 1
  congr 2
  funext k
  simp only [Function.comp_apply, Pi.mulSingle_apply]
  have he : Equiv.swap i j k = j ↔ k = i := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  simp [he]

theorem character_diagonal_determinant (χ : GL n F →* C)
    (i : n) (d : n → Fˣ) :
    χ (diagonalMatrixUnits F d) =
      χ (coordinateDiagonalUnits F i (∏ j, d j)) := by
  calc
    χ (diagonalMatrixUnits F d) =
        ∏ j, χ (coordinateDiagonalUnits F j (d j)) := by
      change (χ.comp (diagonalMatrixUnits F)) d =
        ∏ j, (χ.comp (diagonalMatrixUnits F)) (Pi.mulSingle j (d j))
      rw [← map_prod, Finset.univ_prod_mulSingle]
    _ = ∏ j, χ (coordinateDiagonalUnits F i (d j)) := by
      apply Finset.prod_congr rfl
      intro j _
      exact character_coordinateDiagonal_eq χ i j (d j)
    _ = χ (coordinateDiagonalUnits F i (∏ j, d j)) := by
      exact (map_prod (χ.comp (coordinateDiagonalUnits F i)) _ _).symm

/-- A transvection as an invertible matrix. -/
def characterTransvectionUnit (t : TransvectionStruct n F) : GL n F :=
  ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩

private theorem character_transvection_scale (χ : GL n F →* C)
    (t : TransvectionStruct n F) (s : Fˣ) :
    χ (characterTransvectionUnit t) =
      χ (characterTransvectionUnit {t with c := (s : F) * t.c}) := by
  let d : n → Fˣ := Pi.mulSingle t.i s
  apply character_eq_of_intertwine χ _ _ (diagonalMatrixUnits F d)
  apply Units.ext
  change diagonal (fun i => (d i : F)) * t.toMatrix =
    ({t with c := (s : F) * t.c} : TransvectionStruct n F).toMatrix *
      diagonal (fun i => (d i : F))
  ext i j
  simp only [diagonal_mul, mul_diagonal, TransvectionStruct.toMatrix,
    transvection, Matrix.add_apply, one_apply, Matrix.single_apply]
  by_cases hi : i = t.i <;> by_cases hj : j = t.j <;> by_cases hij : i = j
    <;> simp_all [d, Pi.mulSingle_apply, t.hij, t.hij.symm, eq_comm]

/-- Over a field with an element other than zero and one, any homomorphism
from GL to a commutative group kills the transvections. -/
theorem character_transvection_eq_one (χ : GL n F →* C)
    (s : F) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (t : TransvectionStruct n F) :
    χ (characterTransvectionUnit t) = 1 := by
  let b : F := t.c / (s - 1)
  let t₁ : TransvectionStruct n F := {t with c := b}
  let t₂ : TransvectionStruct n F := {t with c := s * b}
  have hb : b + t.c = s * b := by
    dsimp [b]
    field_simp [sub_ne_zero.mpr hs1]
    ring
  have hscale : χ (characterTransvectionUnit t₁) =
      χ (characterTransvectionUnit t₂) :=
    character_transvection_scale χ t₁ (Units.mk0 s hs0)
  have hmul : characterTransvectionUnit t₁ * characterTransvectionUnit t =
      characterTransvectionUnit t₂ := by
    apply Units.ext
    change transvection t.i t.j b * transvection t.i t.j t.c =
      transvection t.i t.j (s * b)
    rw [transvection_mul_transvection_same _ _ t.hij, hb]
  have he : χ (characterTransvectionUnit t₁) * χ (characterTransvectionUnit t) =
      χ (characterTransvectionUnit t₁) := by
    rw [← map_mul, hmul, ← hscale]
  exact mul_left_cancel (he.trans (mul_one _).symm)

/-- Every homomorphism from GL to a commutative group over a field with more
than two elements factors through the determinant. -/
theorem fieldCharacter_determinantFactor (χ : GL n F →* C)
    (s : F) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (i : n) (g : GL n F) :
    χ g = χ (coordinateDiagonalUnits F i (Matrix.GeneralLinearGroup.det g)) := by
  let P : Matrix n n F → Prop := fun A =>
    ∀ u : GL n F, u.val = A →
      χ u = χ (coordinateDiagonalUnits F i (Matrix.GeneralLinearGroup.det u))
  apply diagonal_transvection_induction_of_det_ne_zero P g.val g.det_ne_zero
    (hdiag := ?_) (htransvec := ?_) (hmul := ?_) g rfl
  · intro d hd u hu
    have hd' : ∀ j, d j ≠ 0 := by
      simpa only [det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies] using hd
    let du : n → Fˣ := fun j => Units.mk0 (d j) (hd' j)
    have he : u = diagonalMatrixUnits F du := Units.ext hu
    rw [he, character_diagonal_determinant χ i du]
    congr 2
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.det, diagonalMatrixUnits_val]
  · intro t u hu
    have he : u = characterTransvectionUnit t := Units.ext hu
    rw [he, character_transvection_eq_one χ s hs0 hs1 t]
    have ht : Matrix.GeneralLinearGroup.det (characterTransvectionUnit t) = 1 := by
      apply Units.ext
      exact t.det
    simp [ht]
  · intro A B hA hB hPA hPB u hu
    let a := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
    let b := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
    have he : u = a * b := Units.ext hu
    rw [he, map_mul, hPA a rfl, hPB b rfl, map_mul, map_mul, map_mul]

end Field

end Langlands.GroupScheme.GeneralLinear
