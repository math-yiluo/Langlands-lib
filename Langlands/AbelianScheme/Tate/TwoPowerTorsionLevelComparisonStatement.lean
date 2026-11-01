import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual torsion levels in a closed abelian subscheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

/-- A closed abelian subscheme containing the actual two-power torsion locus
has the same actual two-power torsion levels. -/
def TwoPowerTorsionLevelComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (A B : AbelianScheme (Spec (CommRingCat.of K))) (f : B ⟶ A),
    IsClosedImmersion (hom f) →
    twoPowerTorsionLocus A ⊆ Set.range (hom f) →
    ∀ n : ℕ, Function.Bijective (GroupScheme.Tate.levelMap
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (groupHom f) (2 ^ n))

end Langlands.AbelianScheme.Tate
