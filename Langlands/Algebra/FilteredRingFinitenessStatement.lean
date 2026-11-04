import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-! # Finiteness descent in filtered Cartesian ring diagrams -/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.FilteredRing

/-- A finite map of filtered colimits descends to a finite map after an actual
arrow from any finite-type stage whose outgoing squares are pushouts. -/
def FiniteTypeFinitenessDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (A B : J ⥤ CommRingCat.{u}) (α : A ⟶ B)
    (cA : Cocone A) (cB : Cocone B)
    (_hcA : IsColimit cA) (_hcB : IsColimit cB)
    (φ : cA.pt ⟶ cB.pt)
    (_hφ : ∀ j, cA.ι.app j ≫ φ = α.app j ≫ cB.ι.app j)
    (j₀ : J) (_hft : (α.app j₀).hom.FiniteType)
    (_hcart : ∀ {k : J} (r : j₀ ⟶ k),
      IsPushout (α.app j₀) (A.map r) (B.map r) (α.app k)),
    φ.hom.Finite → ∃ (k : J) (_r : j₀ ⟶ k), (α.app k).hom.Finite

end Langlands.Algebra.FilteredRing
