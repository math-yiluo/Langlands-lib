import Langlands.BushnellKutzko.LevelZeroBlocks

/-! # Elementary two-block elements and their identities -/

open Matrix

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] {f : ℕ}

/-- The upper unipotent `2 × 2` block matrix with upper right block `X`. -/
def upperU (X : Matrix (Fin f) (Fin f) F) : GL (Fin f ⊕ Fin f) F :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

/-- The lower unipotent `2 × 2` block matrix with lower left block `Y`. -/
def lowerU (Y : Matrix (Fin f) (Fin f) F) : GL (Fin f ⊕ Fin f) F :=
  ⟨fromBlocks 1 0 Y 1, fromBlocks 1 0 (-Y) 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

/-- The block diagonal `2 × 2` block matrix. -/
def diagU (A D : GL (Fin f) F) : GL (Fin f ⊕ Fin f) F :=
  ⟨fromBlocks (A : Matrix (Fin f) (Fin f) F) 0 0 (D : Matrix (Fin f) (Fin f) F),
    fromBlocks ((A⁻¹ : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) 0 0
      ((D⁻¹ : GL (Fin f) F) : Matrix (Fin f) (Fin f) F),
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

/-- The block transposition. -/
def swapU : GL (Fin f ⊕ Fin f) F :=
  ⟨fromBlocks 0 1 1 0, fromBlocks 0 1 1 0, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

/-- `1 + T` for a square-zero `T`. -/
def unipU (T : Matrix (Fin f) (Fin f) F) (hT : T * T = 0) : GL (Fin f) F :=
  ⟨1 + T, 1 - T, by rw [mul_sub, add_mul, add_mul, hT]; simp,
    by rw [sub_mul, mul_add, mul_add, hT]; simp⟩

@[simp] theorem coe_upperU (X : Matrix (Fin f) (Fin f) F) :
    ((upperU X : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) = fromBlocks 1 X 0 1 := rfl

@[simp] theorem coe_lowerU (Y : Matrix (Fin f) (Fin f) F) :
    ((lowerU Y : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) = fromBlocks 1 0 Y 1 := rfl

@[simp] theorem coe_diagU (A D : GL (Fin f) F) :
    ((diagU A D : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) =
      fromBlocks (A : Matrix (Fin f) (Fin f) F) 0 0 (D : Matrix (Fin f) (Fin f) F) := rfl

@[simp] theorem coe_swapU :
    ((swapU : GL (Fin f ⊕ Fin f) F) : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) = fromBlocks 0 1 1 0 := rfl

@[simp] theorem coe_unipU (T : Matrix (Fin f) (Fin f) F) (hT : T * T = 0) :
    ((unipU T hT : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) = 1 + T := rfl

theorem swapU_mul_swapU : (swapU : GL (Fin f ⊕ Fin f) F) * swapU = 1 := by
  ext1
  simp [fromBlocks_multiply]

theorem swapU_inv : (swapU : GL (Fin f ⊕ Fin f) F)⁻¹ = swapU :=
  inv_eq_of_mul_eq_one_left swapU_mul_swapU

theorem swapU_lowerU_swapU (Y : Matrix (Fin f) (Fin f) F) :
    swapU * lowerU Y * swapU = upperU Y := by
  ext1
  simp [fromBlocks_multiply]

theorem upperU_mul (X X' : Matrix (Fin f) (Fin f) F) :
    upperU X * upperU X' = upperU (X + X') := by
  ext1
  simp [fromBlocks_multiply, add_comm]

theorem upperU_eq_of_isUnit (X : GL (Fin f) F) :
    upperU (X : Matrix (Fin f) (Fin f) F) =
      lowerU ((X⁻¹ : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) * swapU * diagU (-X⁻¹) X *
        lowerU ((X⁻¹ : GL (Fin f) F) : Matrix (Fin f) (Fin f) F) := by
  ext1
  simp [fromBlocks_multiply]

theorem lowerU_mul_upperU {Z E : Matrix (Fin f) (Fin f) F} (hZE : Z * E = 0) :
    lowerU Z * upperU E =
      upperU E * diagU (unipU (-(E * Z)) (by
        rw [neg_mul_neg, mul_assoc, ← mul_assoc Z, hZE]; simp)) 1 * lowerU Z := by
  ext1
  simp only [Units.val_mul, coe_lowerU, coe_upperU, coe_diagU, coe_unipU, Units.val_one,
    fromBlocks_multiply]
  congr 1 <;> simp [hZE, mul_add]

theorem diagU_upperU_conj (A D : GL (Fin f) F) (E : Matrix (Fin f) (Fin f) F) :
    diagU A D * upperU E * (diagU A D)⁻¹ =
      upperU ((A : Matrix (Fin f) (Fin f) F) * E * ((D⁻¹ : GL (Fin f) F) : Matrix _ _ F)) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext1
  simp [fromBlocks_multiply, mul_assoc]

end Langlands.BushnellKutzko.LevelZero
