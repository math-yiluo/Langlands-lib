import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType

/-! # Finite type module flatness descends to a finite subalgebra -/

universe uR₀ uR uB₀ uM₀

open scoped TensorProduct

namespace Langlands.Algebra

/-- A finite module over a finite type algebra over a noetherian starting ring, flat after
scalar extension, is already flat over a finite subalgebra containing any prescribed finite set. -/
def FiniteTypeModuleFlatnessDescentStatement : Prop :=
  ∀ (R₀ : Type uR₀) (R : Type uR) (B₀ : Type uB₀) (M₀ : Type uM₀)
    [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    [AddCommGroup M₀] [Module R₀ M₀] [Module B₀ M₀] [IsScalarTower R₀ B₀ M₀]
    [Module.Finite B₀ M₀] [Module.Flat R (R ⊗[R₀] M₀)] (s : Finset R),
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧
      Module.Flat R₁ (R₁ ⊗[R₀] M₀)

end Langlands.Algebra
