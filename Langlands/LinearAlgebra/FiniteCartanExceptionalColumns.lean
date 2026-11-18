import Langlands.LinearAlgebra.FiniteCartanClassicalColumns

/-! # Positive integral columns for exceptional Cartan matrices -/

open Matrix

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

/-- The positive integral column matrix for type E6, scaled by 3. -/
def E6_columnMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, 3, 5, 6, 4, 2;
    3, 6, 6, 9, 6, 3;
    5, 6, 10, 12, 8, 4;
    6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5;
    2, 3, 4, 6, 5, 4]

theorem E6_columnMatrix_nonneg :
    ∀ i j, 0 ≤ E6_columnMatrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem E6_columnMatrix_mul :
    (CartanMatrix.E 6) * E6_columnMatrix = (3 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide

/-- The positive integral column matrix for type E7, scaled by 2. -/
def E7_columnMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  !![4, 4, 6, 8, 6, 4, 2;
    4, 7, 8, 12, 9, 6, 3;
    6, 8, 12, 16, 12, 8, 4;
    8, 12, 16, 24, 18, 12, 6;
    6, 9, 12, 18, 15, 10, 5;
    4, 6, 8, 12, 10, 8, 4;
    2, 3, 4, 6, 5, 4, 3]

theorem E7_columnMatrix_nonneg :
    ∀ i j, 0 ≤ E7_columnMatrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem E7_columnMatrix_mul :
    (CartanMatrix.E 7) * E7_columnMatrix = (2 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  decide

/-- The positive integral column matrix for type E8, scaled by 1. -/
def E8_columnMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
    5, 8, 10, 15, 12, 9, 6, 3;
    7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6;
    8, 12, 16, 24, 20, 15, 10, 5;
    6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3;
    2, 3, 4, 6, 5, 4, 3, 2]

theorem E8_columnMatrix_nonneg :
    ∀ i j, 0 ≤ E8_columnMatrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem E8_columnMatrix_mul :
    (CartanMatrix.E 8) * E8_columnMatrix = (1 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  decide

/-- The positive integral column matrix for type F4, scaled by 1. -/
def F4_columnMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 3, 4, 2;
    3, 6, 8, 4;
    2, 4, 6, 3;
    1, 2, 3, 2]

theorem F4_columnMatrix_nonneg :
    ∀ i j, 0 ≤ F4_columnMatrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem F4_columnMatrix_mul :
    (CartanMatrix.F₄) * F4_columnMatrix = (1 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide

/-- The positive integral column matrix for type G2, scaled by 1. -/
def G2_columnMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, 3;
    1, 2]

theorem G2_columnMatrix_nonneg :
    ∀ i j, 0 ≤ G2_columnMatrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem G2_columnMatrix_mul :
    (CartanMatrix.G₂) * G2_columnMatrix = (1 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  decide

theorem leafExtension_E6_hasCartanMatrix {k : Fin 6} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.E 6) k a b).IsFiniteCartan) (ha : a < 0) :
    HasCartanMatrix (leafExtension (CartanMatrix.E 6) k a b) (CartanMatrix.E 7) := by
  have hp := leafExtension_columnMatrix_bound hE ha.le (by norm_num : (0 : ℤ) < 3)
    E6_columnMatrix_nonneg E6_columnMatrix_mul
  have hpairs := leafExtension_negative_pairs hE ha
  fin_cases k <;>
    rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    norm_num [E6_columnMatrix] at hp
  · refine ⟨Equiv.ofBijective
      (fun i : Fin 7 => ![(5 : Fin 7), 1, 4, 3, 2, 0, 6] i) (by decide), ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · refine ⟨Equiv.refl _, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> decide

theorem leafExtension_E7_hasCartanMatrix {k : Fin 7} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.E 7) k a b).IsFiniteCartan) (ha : a < 0) :
    HasCartanMatrix (leafExtension (CartanMatrix.E 7) k a b) (CartanMatrix.E 8) := by
  have hp := leafExtension_columnMatrix_bound hE ha.le (by norm_num : (0 : ℤ) < 2)
    E7_columnMatrix_nonneg E7_columnMatrix_mul
  have hpairs := leafExtension_negative_pairs hE ha
  fin_cases k <;>
    rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    norm_num [E7_columnMatrix] at hp
  refine ⟨Equiv.refl _, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem not_finiteCartan_leafExtension_E8 {k : Fin 8} {a b : ℤ}
    (ha : a < 0) : ¬ (leafExtension (CartanMatrix.E 8) k a b).IsFiniteCartan := by
  intro hE
  have hp := leafExtension_columnMatrix_bound hE ha.le (by norm_num : (0 : ℤ) < 1)
    E8_columnMatrix_nonneg E8_columnMatrix_mul
  have hpairs := leafExtension_negative_pairs hE ha
  fin_cases k <;>
    rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    norm_num [E8_columnMatrix] at hp

theorem not_finiteCartan_leafExtension_F4 {k : Fin 4} {a b : ℤ}
    (ha : a < 0) : ¬ (leafExtension CartanMatrix.F₄ k a b).IsFiniteCartan := by
  intro hE
  have hp := leafExtension_columnMatrix_bound hE ha.le (by norm_num : (0 : ℤ) < 1)
    F4_columnMatrix_nonneg F4_columnMatrix_mul
  have hpairs := leafExtension_negative_pairs hE ha
  fin_cases k <;>
    rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    norm_num [F4_columnMatrix] at hp

theorem not_finiteCartan_leafExtension_G2 {k : Fin 2} {a b : ℤ}
    (ha : a < 0) : ¬ (leafExtension CartanMatrix.G₂ k a b).IsFiniteCartan := by
  intro hE
  have hp := leafExtension_columnMatrix_bound hE ha.le (by norm_num : (0 : ℤ) < 1)
    G2_columnMatrix_nonneg G2_columnMatrix_mul
  have hpairs := leafExtension_negative_pairs hE ha
  fin_cases k <;>
    rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    norm_num [G2_columnMatrix] at hp

end Langlands.LinearAlgebra.FiniteCartanMatrix
