import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Unitary.ConjugateSpace
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Complex conjugation commutes with compact induction on a compact quotient -/

namespace Langlands.Renard.CompactRepresentation

open Induction

universe u v

/-- Renard IV.2.1, paragraph after Remark 2. For a closed cocompact subgroup,
conjugation of the inducing representation agrees with conjugation after
unnormalized compact induction. The comparison is pointwise conjugation
into the conjugate coefficient space. -/
def CompactInductionConjugateStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G), IsClosed (H : Set G) → CompactSpace (LeftQuotient H) →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ H V), IsSmooth ρ →
      ∃ e : (ConjSpace.rep (compactInduced H ρ)).Equiv
          (compactInduced H (ConjSpace.rep ρ)),
        ∀ (f : CompactFunctions H ρ) (x : G),
          eval H (ConjSpace.rep ρ) (e (ConjSpace.equiv _ f)).val x =
            ConjSpace.equiv V (eval H ρ f.val x)

end Langlands.Renard.CompactRepresentation
