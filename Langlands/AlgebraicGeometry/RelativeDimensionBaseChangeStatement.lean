import Langlands.AlgebraicGeometry.RelativeDimensionLoci

/-! # Relative local dimension and sublevels under arbitrary base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Stacks Lemma 29.29.3(1) and its actual sublevel inverse-image consequence. -/
def RelativeDimensionBaseChangeInvariance : Prop :=
  ∀ {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [LocallyOfFiniteType f],
    IsPullback a b f g →
      (∀ x : P, relativeTopologicalKrullDimAt b x =
        relativeTopologicalKrullDimAt f (a x)) ∧
      (∀ n : ℕ, relativeDimensionSublevel b n = a ⁻¹' relativeDimensionSublevel f n)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
