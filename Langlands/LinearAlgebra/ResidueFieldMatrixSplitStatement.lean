import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Splitting a matrix near an injective residue-field specialization -/

universe u

noncomputable section

namespace Langlands.LinearAlgebra

/-- A rectangular matrix injective over a residue field has a left inverse
after inverting one element outside the corresponding prime ideal. -/
def ResidueFieldMatrixSplitStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) R),
    Function.Injective (A.map (algebraMap R p.ResidueField)).mulVec →
      ∃ r : R, r ∉ p ∧
        ∃ B : Matrix (Fin n) (Fin m) (Localization.Away r),
          B * A.map (algebraMap R (Localization.Away r)) = 1

end Langlands.LinearAlgebra
