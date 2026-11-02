import Langlands.Algebra.NonUnitalSeparationStatements
import Langlands.Algebra.NonnilpotentLeftResolventProof

/-!
# Renard B.III: the one-sided shift of an original nonunital element

Transfer the rank and positive-product nilpotence conditions to the actual
scalar unitization and apply the published unital one-sided resolvent theorem.
-/

set_option autoImplicit false

universe uA

namespace Langlands.Renard

open Langlands.Algebra

/-- The original nonunital one-sided resolvent, without extra assumptions on `A`. -/
theorem nonUnitalNonnilpotentLeftResolvent (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] :
    NonUnitalNonnilpotentLeftResolventStatement A := by
  intro hrank a ha
  exact nonnilpotentLeftResolvent (Unitization ℂ A)
    ((unitization_countableRank_iff ℂ A).2 hrank) (Unitization.inr a)
    (fun h => ha ((isNilpotent_inr_iff ℂ a).1 h))

end Langlands.Renard
