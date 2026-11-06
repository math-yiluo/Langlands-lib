import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Transporting a morphism property across an isomorphism over the base -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

/-- A morphism property respecting isomorphisms transfers across an isomorphism over the base. -/
theorem prop_hom_of_overIso (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    {V : Scheme.{u}} {X Y : Over V} (e : X ≅ Y) (h : Q Y.hom) : Q X.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget V).mapIso e).hom)
  rw [← Over.w e.hom, Q.cancel_left_of_respectsIso]
  exact h

end Langlands.AlgebraicGeometry
