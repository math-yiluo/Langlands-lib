import Langlands.HarmonicAnalysis.RenardHomogeneousQuotientProof
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Unitary.ConjugateSpace

/-! # The relative-modulus correction in the unnormalized Hermitian dual -/

namespace Langlands.Renard.CompactRepresentation

open Induction HarmonicAnalysis.HomogeneousFunctions

universe u v

/-- Renard IV.2.1, the displayed calculation before (IV.2.1.1). The induction
of the Hermitian dual is the Hermitian dual of induction after twisting by
the full relative modulus. -/
def UnnormalizedInductionHermitianDualityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)), CompactSpace (LeftQuotient H) →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ H V), IsSmooth ρ →
      let δ := HarmonicAnalysis.HomogeneousFunctions.Renard.relativeCharacter H hH
      let hermitianDual := ConjSpace.rep (smoothContragredient ρ)
      let inducedDual := (compactInductionFunctor H).obj (Rep.of hermitianDual)
      let twistedInduction := (compactInductionFunctor H).obj (Rep.of (twist δ.toMonoidHom ρ))
      Nonempty (inducedDual.representation.Equiv
        (ConjSpace.rep (smoothContragredient twistedInduction.representation)))

end Langlands.Renard.CompactRepresentation
