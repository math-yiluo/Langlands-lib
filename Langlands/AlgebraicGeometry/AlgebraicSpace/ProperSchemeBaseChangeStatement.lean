import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange

/-! # Proper algebraic-space morphisms under a change of base scheme -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Properness is preserved by arbitrary change of the base scheme. This is the
scheme-base specialization of Stacks, Tag 04WP. -/
def ProperSchemeBaseChangeStatement : Prop :=
  ∀ (S T : Scheme.{u}) (g : T ⟶ S) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsProperMorphism f → IsProperMorphism (baseChangeMap g f)

end Langlands.AlgebraicGeometry.AlgebraicSpace
