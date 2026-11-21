import Langlands.Representation.Smooth.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Continuous unitary representations of t.d. groups need not be smooth -/

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.2.2, opening paragraph. A continuous unitary representation on a
complex Hilbert space can fail to be smooth even for a t.d. group. -/
def ContinuousUnitaryNonsmoothCounterexampleStatement : Prop :=
  ¬ ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
      (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (ρ : Representation ℂ G E),
      (∀ v : E, Continuous (fun g : G => ρ g v)) →
      (∀ (g : G) (v w : E), inner ℂ (ρ g v) (ρ g w) = inner ℂ v w) →
        IsSmooth ρ

end Langlands.Renard.CompactRepresentation
