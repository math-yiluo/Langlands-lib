import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.LocallyConstant.Basic

/-! A Baire constancy statement for finite-dimensional function germs. -/

namespace Langlands.Topology

universe uX uY

set_option linter.unusedVariables false in
/-- A pointwise locally constant family with finite-dimensional eventual germs
has its assigned germ representative constant on a nonempty open parameter set. -/
def BaireFiniteDimensionalGermConstancyStatement : Prop :=
  ∀ (X : Type uX) (Y : Type uY) [TopologicalSpace Y]
    [BaireSpace Y] [Nonempty Y]
    (D : ℕ → Set X) (hD : Antitone D)
    (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V],
    (∀ m : ℕ, Function.Injective
      (fun v : V => fun x : D m => (v : X → ℂ) x)) →
    ∀ (f : Y → X → ℂ) (v : Y → V),
      (∀ x : X, IsLocallyConstant (fun y : Y => f y x)) →
      (∀ y : Y, ∃ m : ℕ, ∀ x ∈ D m, f y x = (v y : X → ℂ) x) →
      ∃ O : Set Y, IsOpen O ∧ O.Nonempty ∧
        ∀ y ∈ O, ∀ z ∈ O, v y = v z

end Langlands.Topology
