import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Tate.PrimeAdic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # Rank and cardinality of actual torsion at a geometric point -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

/-- For a positive integer invertible on the base, the actual torsion at an
algebraically closed point is a free residue module of rank twice the relative
dimension, with the corresponding cardinality. This is a proof target. -/
def GeometricTorsionRankStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (g : ℕ),
    A.HasRelativeDimension g →
      ∀ (n : ℕ), 0 < n → IsUnit (n : Γ(S, ⊤)) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s : Spec (CommRingCat.of Ω) ⟶ S),
          Nonempty ((Fin (2 * g) → ZMod n) ≃ₗ[ZMod n]
            GroupScheme.Tate.Level A.toGrp (Over.mk s) n) ∧
              Nat.card (GroupScheme.Tate.Level A.toGrp (Over.mk s) n) = n ^ (2 * g)

end Langlands.AbelianScheme.Tate
