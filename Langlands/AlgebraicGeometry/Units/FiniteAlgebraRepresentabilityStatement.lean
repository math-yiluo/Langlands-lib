import Langlands.AlgebraicGeometry.Units.FiniteAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Representability and smoothness of actual finite-algebra units -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.FiniteAlgebraUnits

/-- The canonical map defined by the actual universal unit represents the unit
presheaf on all schemes over the field, and its actual candidate is smooth. -/
def RepresentabilityStatement : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (n : ℕ) (b : Module.Basis (Fin n) k A),
    IsIso (candidateMap b) ∧
      _root_.AlgebraicGeometry.Smooth (candidate b).hom

end Langlands.AlgebraicGeometry.FiniteAlgebraUnits
