import Langlands.LocalFactor.Ramification.InertiaPresentation
import Langlands.Weil.Representation.Predicates

/-!
# Integrality of the conductors of every presentation of a local Weil representation

A complex representation of the local Weil group of a p-adic field is presented on a finite
quotient of inertia by a finite Galois subextension whose restriction kernel acts trivially
(`Ramification.Padic.FiniteInertiaPresentation`). The statement says that every such presentation
with surjective inertia restriction has natural Artin and Swan expressions, for every
representation, and that every continuous representation has such a presentation.
Proposition definition only.
-/

namespace Langlands.Henniart

open Ramification.Padic Weil.Local

universe uF uV

/-- **Integrality for every presentation of every Weil representation.** For every
finite-dimensional complex representation `A` of the local Weil group of a p-adic field `F`:
every finite inertia presentation of `A` with surjective inertia restriction has natural Artin and
Swan expressions; and if `A` is continuous, it has such a presentation. -/
def WeilConductorIntegralityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)),
    (∀ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
      (∃ a : ℕ, P.artinConductor hP = (a : ℚ)) ∧ (∃ s : ℕ, P.swanConductor hP = (s : ℚ))) ∧
    (A.IsContinuous →
      ∃ (P : FiniteInertiaPresentation F A)
        (hP : Function.Surjective (weilInertiaRestriction F P.extension)) (a s : ℕ),
        P.artinConductor hP = (a : ℚ) ∧ P.swanConductor hP = (s : ℚ))

end Langlands.Henniart
