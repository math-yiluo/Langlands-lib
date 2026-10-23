import Langlands.Representation.RankinSelberg.RootCoordinateStatement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The inverse Borel-modulus weight in finite-function torus coordinates. -/

namespace Langlands.RankinSelberg

open scoped BigOperators

universe uF

/-- The explicit inverse root-coordinate modulus is continuous and
multiplicative. Multiplying it by two finite functions pulled back to root
coordinates preserves continuity and finite-dimensional translation span. -/
def RootCoordinateFiniteFunctionStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  let A := Fin (n + 1) → F.Carrierˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let finiteFunction := fun f : A → ℂ => Continuous f ∧
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : A => fun a : A => f (b * a)))
  Continuous weight ∧ weight 1 = 1 ∧
    (∀ a b : A, weight (a * b) = weight a * weight b) ∧
    ∀ f g : A → ℂ, finiteFunction f → finiteFunction g →
      finiteFunction (fun a => f (toDiagonal a) * g (toDiagonal a) * weight a)

end Langlands.RankinSelberg
