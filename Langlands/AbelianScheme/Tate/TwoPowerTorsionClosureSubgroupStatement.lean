import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Section subgroup of the actual two-power torsion closure -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

/-- The actual rational sections whose image belongs to the Zariski closure
of the actual two-power torsion form a subgroup. Translation by any such
section preserves that closed subset. -/
def TwoPowerTorsionClosureSubgroupStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
    ∃ H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
      (∀ s, s ∈ H ↔ s.left (default : Spec (CommRingCat.of K)) ∈
        closure (twoPowerTorsionLocus A)) ∧
      ∀ s ∈ H, (GrpObj.mulRight s).hom.left '' closure (twoPowerTorsionLocus A) =
        closure (twoPowerTorsionLocus A)

end Langlands.AbelianScheme.Tate
