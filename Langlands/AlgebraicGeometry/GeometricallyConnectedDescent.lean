import Langlands.AlgebraicGeometry.GeometricallyConnectedDescentStatement
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

/-! # Descent of geometric connectedness along a surjective base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Geometric connectedness descends along any surjective change of base. -/
theorem geometricallyConnected_of_surjective_baseChange
    [Surjective g] [GeometricallyConnected (pullback.snd f g)] :
    GeometricallyConnected f := by
  have : MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective :=
    GeometricallyConnected.descendsAlong_surjective
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @GeometricallyConnected) (Q := @Surjective)
    (inferInstance : Surjective g) inferInstance

/-- The descent lemma for an arbitrary pullback square. -/
theorem geometricallyConnected_of_surjective_isPullback
    {P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    (h : IsPullback a b f g) [Surjective g] [GeometricallyConnected b] :
    GeometricallyConnected f := by
  have : MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective :=
    GeometricallyConnected.descendsAlong_surjective
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @GeometricallyConnected) (Q := @Surjective) h.flip
    (inferInstance : Surjective g) inferInstance

/-- The exact universe-polymorphic proposition target. -/
theorem geometricallyConnectedSurjectiveDescent :
    GeometricallyConnectedSurjectiveDescentStatement.{u} := by
  intro X Y S f g hg hf
  have := hg
  have := hf
  exact geometricallyConnected_of_surjective_baseChange f g

end Langlands.AlgebraicGeometry
