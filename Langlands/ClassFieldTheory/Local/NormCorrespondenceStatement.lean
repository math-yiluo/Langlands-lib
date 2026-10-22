import Langlands.LocalField.Definitions
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.Norm.Basic

/-! # The norm-subgroup correspondence and separation

These proposition definitions use actual intermediate fields and norm images.
They assert no theorem and assume no reciprocity map.
-/

namespace Langlands.LocalClassField

universe u

/-- The finite abelian extension correspondence reverses inclusion and
exchanges the two lattice operations. -/
def NormSubgroupLattice : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E₁ E₂ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    [FiniteDimensional F.Carrier E₁] [FiniteDimensional F.Carrier E₂]
    [IsAbelianGalois F.Carrier E₁] [IsAbelianGalois F.Carrier E₂],
    let N := fun E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) =>
      (Units.map (Algebra.norm F.Carrier (S := E))).range
    (E₁ ≤ E₂ ↔ N E₂ ≤ N E₁) ∧
      N (E₁ ⊔ E₂) = N E₁ ⊓ N E₂ ∧
      N (E₁ ⊓ E₂) = N E₁ ⊔ N E₂

/-- A nonidentity element is excluded by the norm subgroup of some finite
abelian extension inside the actual algebraic closure. -/
def NormSubgroupsSeparatePoints : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (a : F.Carrierˣ), a ≠ 1 →
    ∃ E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier),
      FiniteDimensional F.Carrier E ∧ IsAbelianGalois F.Carrier E ∧
        a ∉ (Units.map (Algebra.norm F.Carrier (S := E))).range

/-- The lattice and separation parts of the local norm-subgroup correspondence. -/
def NormCorrespondenceProperties : Prop :=
  NormSubgroupLattice.{u} ∧ NormSubgroupsSeparatePoints.{u}

end Langlands.LocalClassField
