import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Solvable

/-! # Cyclic prime-step towers for finite solvable Galois extensions -/

namespace Langlands.FieldTheory

universe u v

/-- Every finite Galois extension with solvable Galois group admits a finite
ascending tower of intermediate fields with cyclic Galois steps of prime degree.
All step properties use the algebra induced by the same inclusion. This is a
proposition target, not a proof. -/
def SolvableGaloisPrimeTower : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable Gal(L/K)],
    ∃ (n : ℕ) (T : Fin (n + 1) → IntermediateField K L),
      T 0 = ⊥ ∧ T (Fin.last n) = ⊤ ∧
      ∀ i : Fin n, ∃ h : T i.castSucc ≤ T i.succ,
        letI : Algebra (T i.castSucc) (T i.succ) :=
          (IntermediateField.inclusion h).toAlgebra
        FiniteDimensional (T i.castSucc) (T i.succ) ∧
          IsGalois (T i.castSucc) (T i.succ) ∧
          IsCyclic ((T i.succ) ≃ₐ[T i.castSucc] (T i.succ)) ∧
          Nat.Prime (Module.finrank (T i.castSucc) (T i.succ))

end Langlands.FieldTheory
