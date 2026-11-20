import Langlands.Correspondence.HenniartCyclicBaseChange
import Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof

/-!
# The Herbrand function of a cyclic prime-degree step as a relative Herbrand function

One proposition definition. It compares two existing Library definitions of the
inverse Herbrand function `ψ_{M/L}` of a cyclic prime-degree step `M/L` of p-adic fields:
`CyclicPrimeStep.herbrandPsi`, computed in `M` itself, and
`HerbrandBridge.relativeHerbrandPsi E`, computed in the Galois closure of a finite
extension `E` of `L` inside `AlgebraicClosure L` that is `L`-isomorphic to `M`.
No proof is given here.
-/

namespace Langlands.Henniart

universe u

open Langlands.LocalClassField

/-- For a cyclic prime-degree step `M/L` and a finite extension `E` of `L` inside
`AlgebraicClosure L` that is `L`-isomorphic to `M`, the step's Herbrand function
`ψ_{M/L}` equals the relative Herbrand function `ψ_{E/L}`. This is a statement, not a
theorem. -/
def CyclicPrimeStepHerbrandPsiStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : Numerical.CyclicPrimeStep.{u} p)
    (E : FiniteIntermediateExtension S.base.Carrier),
    (letI := S.algebra
     Nonempty (S.top.Carrier ≃ₐ[S.base.Carrier] E.field)) →
    S.herbrandPsi = Ramification.HerbrandBridge.relativeHerbrandPsi E

end Langlands.Henniart
