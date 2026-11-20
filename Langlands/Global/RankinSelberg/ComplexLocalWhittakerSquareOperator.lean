import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.ComplexLocalEllipticAnnihilator

/-! # The coordinate square operator on complex Whittaker coefficients -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Archimedean.ComplexLocalCasimir
open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "I" => Fin (r + 1)
local notation "M" => Matrix I I ℂ
local notation "R" => rightDerivative (matrixModel ℂ (r + 1))
local notation "Std" => Automorphic.complexStandardKFinite (r + 1)

/-- The sum of two successive right derivatives in each real and imaginary
matrix-unit direction. -/
def complexCoordinateSquareDifferential (W : G → ℂ) (g : G) : ℂ :=
  (∑ i : I, ∑ j : I, R (Matrix.single i j 1) (R (Matrix.single i j 1) W) g) +
    (∑ i : I, ∑ j : I, R (Matrix.single i j Complex.I) (R (Matrix.single i j Complex.I) W) g)

/-- An intertwiner sends the coordinate square operator on the inducing vector
to its differential action on the output function. -/
theorem complexCoordinateSquareDifferential_intertwiner {ds : List ComplexCharacterData} {a : ℂˣ}
    {B : Std ds →ₗ[ℂ] (G → ℂ)} (hB : IsComplexWhittakerIntertwiner r ds a B)
    (f : Std ds) :
    B (coordinateSquareOperator ds f) = complexCoordinateSquareDifferential (B f) := by
  let A := envelopingAction (complexStandardLie (r + 1) ds)
  have hder (X : M) (v : Std ds) : B (A (realGenerator (r + 1) X) v) = R X (B v) :=
    hB.2.2.2.2 X v (A (realGenerator (r + 1) X) v) (realGenerator_action ds X v)
  have hsq (X : M) :
      B (A (realGenerator (r + 1) X ^ 2) f) = R X (R X (B f)) := by
    rw [map_pow, pow_two, Module.End.mul_apply, hder, hder]
  funext g
  simp only [coordinateSquareOperator, coordinateSquareSum, map_add, map_sum,
    LinearMap.add_apply, LinearMap.sum_apply, complexCoordinateSquareDifferential,
    Pi.add_apply, Finset.sum_apply]
  change
    (∑ i : I, ∑ j : I, B (A (realGenerator (r + 1) (Matrix.single i j 1) ^ 2) f) g) +
      (∑ i : I, ∑ j : I, B (A (realGenerator (r + 1) (Matrix.single i j Complex.I) ^ 2) f) g) = _
  simp only [hsq]

end Langlands.Global.RankinSelbergGlobal
