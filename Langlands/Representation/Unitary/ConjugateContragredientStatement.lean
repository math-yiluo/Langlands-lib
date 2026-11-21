import Langlands.Representation.Unitary.ConjugateSpace
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Complex conjugation commutes with the smooth contragredient -/

namespace Langlands.Renard.CompactRepresentation

universe u v

/-- Renard IV.2.1, opening paragraph. The conjugate of the smooth contragredient
identifies with the smooth contragredient of the conjugate by conjugating the
evaluation of each functional on the underlying vector. -/
def ConjugateContragredientStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ →
    ∃ e : (ConjSpace.rep (smoothContragredient ρ)).Equiv
        (smoothContragredient (ConjSpace.rep ρ)),
      ∀ (ℓ : SmoothDual ρ) (x : V),
        (e (ConjSpace.equiv _ ℓ)).val (ConjSpace.equiv V x) =
          starRingEnd ℂ (ℓ.val x)

end Langlands.Renard.CompactRepresentation
