import Langlands.GroupScheme.MatrixRepresentation.NormalKernelTensor
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces

/-! # Positive tensor powers and their line stabilizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

/-- Coordinates for a positive tensor power: the parameter `r` denotes degree `r + 1`. -/
@[reducible] def PositiveTensorIndex (n : Type) : ℕ → Type
  | 0 => n
  | r + 1 => n × PositiveTensorIndex n r

@[reducible] instance positiveTensorIndexFintype (n : Type) [Fintype n] (r : ℕ) :
    Fintype (PositiveTensorIndex n r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype n)
  | succ r ih =>
      letI := ih
      exact inferInstanceAs (Fintype (n × PositiveTensorIndex n r))

@[reducible] instance positiveTensorIndexDecidableEq (n : Type) [DecidableEq n] (r : ℕ) :
    DecidableEq (PositiveTensorIndex n r) := by
  induction r with
  | zero => exact inferInstanceAs (DecidableEq n)
  | succ r ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (n × PositiveTensorIndex n r))

/-- The repeated pure tensor of a vector, in degree `r + 1`. -/
def positiveTensorVector {A : Type*} [Mul A] {n : Type} (v : n → A) :
    (r : ℕ) → PositiveTensorIndex n r → A
  | 0 => v
  | r + 1 => fun ij => v ij.1 * positiveTensorVector v r ij.2

/-- The diagonal coordinate of the repeated pure tensor. -/
def positiveTensorDiagonal {n : Type} (j : n) : (r : ℕ) → PositiveTensorIndex n r
  | 0 => j
  | r + 1 => (j, positiveTensorDiagonal j r)

section Coordinates

variable {A B : Type*} [CommRing A] [CommRing B] {n : Type}

/-- Repeated pure tensors commute with coefficient maps. -/
theorem positiveTensorVector_map (f : A →+* B) (v : n → A) (r : ℕ) :
    positiveTensorVector (fun j => f (v j)) r =
      fun j => f (positiveTensorVector v r j) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      funext ij
      simp only [positiveTensorVector, ih, map_mul]

/-- A coordinate normalized to one remains normalized in every positive tensor power. -/
theorem positiveTensorVector_diagonal (v : n → A) (j : n) (hv : v j = 1) (r : ℕ) :
    positiveTensorVector v r (positiveTensorDiagonal j r) = 1 := by
  induction r with
  | zero => exact hv
  | succ r ih => simpa only [positiveTensorVector, positiveTensorDiagonal, hv, one_mul] using ih

/-- A scalar acts on the repeated pure tensor by its positive degree. -/
theorem positiveTensorVector_smul (a : A) (v : n → A) (r : ℕ) :
    positiveTensorVector (a • v) r = (a ^ (r + 1)) • positiveTensorVector v r := by
  induction r with
  | zero =>
      simp only [zero_add, pow_one, positiveTensorVector]
  | succ r ih =>
      funext ij
      simp only [positiveTensorVector, ih, Pi.smul_apply, smul_eq_mul]
      rw [pow_succ]
      ring

/-- A unit multiple of a normalized repeated pure tensor detects the original line,
even over rings with nilpotents. -/
theorem exists_unit_smul_of_positiveTensorVector
    (v v' : n → A) (j : n) (hv : v j = 1) (r : ℕ) (a : Aˣ)
    (h : positiveTensorVector v' r = (a : A) • positiveTensorVector v r) :
    ∃ b : Aˣ, v' = (b : A) • v := by
  cases r with
  | zero => exact ⟨a, h⟩
  | succ r =>
      apply exists_unit_smul_of_pureTensor_eq v v'
        (positiveTensorVector v r) ((a⁻¹ : Aˣ) • positiveTensorVector v' r)
        j (positiveTensorDiagonal j r) hv (positiveTensorVector_diagonal v j hv r)
      funext ij
      have hij := congrFun h ij
      change v' ij.1 * ((↑(a⁻¹) : A) * positiveTensorVector v' r ij.2) =
        v ij.1 * positiveTensorVector v r ij.2
      change v' ij.1 * positiveTensorVector v' r ij.2 =
        (a : A) * (v ij.1 * positiveTensorVector v r ij.2) at hij
      calc
        _ = (↑(a⁻¹) : A) * (v' ij.1 * positiveTensorVector v' r ij.2) := by ring
        _ = _ := by rw [hij, ← mul_assoc, Units.inv_mul, one_mul]

end Coordinates

section SchemeRepresentations

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual positive tensor power of a finite matrix representation. -/
def positiveTensorPower (ρ : MatrixRepresentation G n) :
    (r : ℕ) → MatrixRepresentation G (PositiveTensorIndex n r)
  | 0 => ρ
  | r + 1 => ρ.tensor (positiveTensorPower ρ r)

/-- Positive tensor powers commute with restriction. -/
theorem positiveTensorPower_restrict (ρ : MatrixRepresentation G n) (i : H ⟶ G) (r : ℕ) :
    (ρ.restrict i).positiveTensorPower r = (ρ.positiveTensorPower r).restrict i := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (ρ.restrict i).tensor ((ρ.restrict i).positiveTensorPower r) = _
      rw [ih, tensor_restrict]
      rfl

/-- Every point acts on a repeated pure tensor by repeating its action on the vector. -/
theorem positiveTensorPower_pointMatrix_mulVec (ρ : MatrixRepresentation G n)
    (T : Over (Spec R)) (x : T ⟶ G.X) (v : n → Γ(T.left, ⊤)) (r : ℕ) :
    ((ρ.positiveTensorPower r).pointMatrix T x :
        Matrix (PositiveTensorIndex n r) (PositiveTensorIndex n r) Γ(T.left, ⊤)) *ᵥ
      positiveTensorVector v r =
        positiveTensorVector ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ v) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [positiveTensorPower, positiveTensorVector]
      rw [tensor_pointMatrix, GeneralLinear.kroneckerHom_mulVec, ih]

/-- The repeated pure tensor action formula in affine coefficient coordinates. -/
theorem positiveTensorPower_affineMatrix_mulVec (ρ : MatrixRepresentation G n)
    (A : CommAlgCat.{u} R) (x : G.affinePoints A) (v : n → A) (r : ℕ) :
    ((ρ.positiveTensorPower r).affineMatrix A x :
        Matrix (PositiveTensorIndex n r) (PositiveTensorIndex n r) A) *ᵥ
      positiveTensorVector v r =
        positiveTensorVector ((ρ.affineMatrix A x : Matrix n n A) *ᵥ v) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [positiveTensorPower, positiveTensorVector]
      rw [tensor_affineMatrix, GeneralLinear.kroneckerHom_mulVec, ih]

/-- The positive tensor power has exactly the original line stabilizer, at every test point. -/
theorem positiveTensorPower_preserves_line_iff (ρ : MatrixRepresentation G n)
    (v : n → R) (j : n) (hv : v j = 1) (r : ℕ)
    (T : Over (Spec R)) (x : T ⟶ G.X) :
    (∃ a : Γ(T.left, ⊤)ˣ,
      ((ρ.positiveTensorPower r).pointMatrix T x :
          Matrix (PositiveTensorIndex n r) (PositiveTensorIndex n r) Γ(T.left, ⊤)) *ᵥ
        (fun s => scalarMap T (positiveTensorVector v r s)) =
          (a : Γ(T.left, ⊤)) •
            (fun s => scalarMap T (positiveTensorVector v r s))) ↔
      ∃ a : Γ(T.left, ⊤)ˣ,
        (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun s => scalarMap T (v s)) =
            (a : Γ(T.left, ⊤)) • (fun s => scalarMap T (v s)) := by
  rw [← positiveTensorVector_map, positiveTensorPower_pointMatrix_mulVec]
  constructor
  · rintro ⟨a, ha⟩
    exact exists_unit_smul_of_positiveTensorVector _ _ j (by rw [hv, map_one]) r a ha
  · rintro ⟨a, ha⟩
    refine ⟨a ^ (r + 1), ?_⟩
    rw [ha, positiveTensorVector_smul, Units.val_pow_eq_pow_val]

end SchemeRepresentations

section CharacterVectors

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The unit of a natural multiple of a rational character is the corresponding power. -/
theorem characterUnit_nsmul (χ : rationalCharacters G) (r : ℕ) :
    CharacterUnits.unit (r • χ) = CharacterUnits.unit χ ^ r := by
  induction r with
  | zero => rw [zero_nsmul, CharacterUnits.unit_zero, pow_zero]
  | succ r ih =>
      rw [succ_nsmul, CharacterUnits.unit_add, ih, pow_succ]

/-- A character vector gives a vector of the positive multiple character in each
actual positive tensor power. -/
theorem positiveTensorPower_characterSpace (ρ : MatrixRepresentation G n)
    {χ : rationalCharacters G} {v : n → k}
    (hv : v ∈ ρ.characterSpace χ) (r : ℕ) :
    positiveTensorVector v r ∈ (ρ.positiveTensorPower r).characterSpace ((r + 1) • χ) := by
  rw [mem_characterSpace_iff]
  unfold universalCharacterMatrix
  rw [← positiveTensorVector_map, positiveTensorPower_affineMatrix_mulVec]
  have he := hv
  rw [mem_characterSpace_iff] at he
  unfold universalCharacterMatrix at he
  rw [he, positiveTensorVector_smul, characterUnit_nsmul, Units.val_pow_eq_pow_val,
    positiveTensorVector_map]

end CharacterVectors

end Langlands.GroupScheme.MatrixRepresentation
