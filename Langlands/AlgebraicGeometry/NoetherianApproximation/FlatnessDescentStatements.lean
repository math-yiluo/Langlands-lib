import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Finite-stage descent of relative module flatness -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Relative flatness of a finitely presented actual module descends to a finite subalgebra
and holds on every realization of the resulting Cartesian square. -/
def IsFlatOverSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A]
    [Algebra A₀ A] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₀] [LocallyOfFiniteType f₀] (M₀ : X₀.Modules),
    M₀.IsFinitePresentation →
    ∀ {X : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ Spec (CommRingCat.of A)),
      IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) →
      Modules.IsFlatOver f ((Scheme.Modules.pullback a).obj M₀) →
    ∀ (s : Finset A), ∃ T : Subalgebra A₀ A, T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ {X' : Scheme.{u}} (a' : X' ⟶ X₀) (f' : X' ⟶ Spec (CommRingCat.of ↥T)),
        IsPullback a' f' f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) →
        Modules.IsFlatOver f' ((Scheme.Modules.pullback a').obj M₀)

end Langlands.AlgebraicGeometry.NoetherianApproximation
