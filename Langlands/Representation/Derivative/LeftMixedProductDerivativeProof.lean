import Langlands.Representation.Derivative.LeftMixedProductHigher
import Langlands.Representation.Derivative.LeftMixedProductVanishing
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi

/-!
# Derivatives of left mixed products in every GL rank

BZ77 Corollary 4.14(a), with the arbitrary-carrier GL₀ case and the
high-order vanishing clause. The positive-rank comparison uses the published
left Psi and Phi compatibility proofs and the published Phi boundary.
-/

namespace Langlands.Derivative

universe uF uV

/-- BZ77 4.14(a): the exact all-rank natural comparison and vanishing statement. -/
theorem leftMixedProductDerivative
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LeftMixedProductDerivative.{uF, uV} F T :=
  ⟨LeftMixedProductHigher.leftMixedProductDerivativeIso T
      (MirabolicProductMinus.leftPhiCompatibility T),
    LeftMixedProductVanishing.leftMixedProductDerivativeVanishing_of_leftPhiCompatibility T
      (MirabolicProductMinus.leftPhiCompatibility T)⟩

/-- The natural comparison in every GL rank and every order `1 ≤ i ≤ r + 1`. -/
theorem leftMixedProductDerivativeIso
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LeftMixedProductDerivativeIso.{uF, uV} F T :=
  (leftMixedProductDerivative F T).1

/-- Every remaining valid order has a subsingleton carrier. -/
theorem leftMixedProductDerivativeVanishing
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LeftMixedProductDerivativeVanishing.{uF, uV} F T :=
  (leftMixedProductDerivative F T).2

end Langlands.Derivative
