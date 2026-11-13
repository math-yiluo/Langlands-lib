import Langlands.Representation.RankinSelberg.RootFiniteFunctionStatement
import Langlands.AllField.Representation.RankinSelberg.RootCoordinateStatement
/-! The inverse Borel-modulus weight in finite-function torus coordinates. -/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding RootCoordinateChangeStatement RootCoordinateFiniteFunctionStatement
open Langlands.AllField.RankinSelberg

open scoped BigOperators

universe uF

/-- The explicit inverse root-coordinate modulus is continuous and
multiplicative. Multiplying it by two finite functions pulled back to root
coordinates preserves continuity and finite-dimensional translation span. -/
def RootCoordinateFiniteFunctionStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  let A := Fin (n + 1) → Fˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let finiteFunction := fun f : A → ℂ => Continuous f ∧
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : A => fun a : A => f (b * a)))
  Continuous weight ∧ weight 1 = 1 ∧
    (∀ a b : A, weight (a * b) = weight a * weight b) ∧
    ∀ f g : A → ℂ, finiteFunction f → finiteFunction g →
      finiteFunction (fun a => f (toDiagonal a) * g (toDiagonal a) * weight a)

end Langlands.AllField.RankinSelberg
