import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-!
# Flat base change for higher direct images

This file states the existence of flat base change isomorphisms for higher direct
images of quasi-coherent modules along quasi-compact separated morphisms.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Existence of flat base change isomorphisms for higher direct images of
quasi-coherent modules along quasi-compact separated morphisms. -/
def FlatHigherDirectImageBaseChangeStatement : Prop :=
  ∀ (X Y X' Y' : Scheme.{u}) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X),
    IsPullback g' f' f g → QuasiCompact f → IsSeparated f → Flat g →
    ∀ (M : X.Modules), M.IsQuasicoherent → ∀ n : ℕ,
      Nonempty ((Scheme.Modules.pullback g).obj
          ((DerivedSections.higherDirectImage f n).obj M) ≅
        (DerivedSections.higherDirectImage f' n).obj ((Scheme.Modules.pullback g').obj M))

end Langlands.AlgebraicGeometry.Modules
