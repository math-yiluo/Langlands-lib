import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Langlands.Representation.Whittaker.BruhatCellDistribution
import Langlands.HarmonicAnalysis.Distribution.SupportedRestriction

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis HarmonicAnalysis.Distribution

universe u

def BruhatCellRestrictionVanishingStatement : Prop :=
  ∀ (n : ℕ) (K : Type u) [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K]
    [LocallyCompactSpace (GeneralLinear (n + 1) K)]
    [TotallyDisconnectedSpace (GeneralLinear (n + 1) K)]
    (w : Equiv.Perm (Fin (n + 1))) (ψ : UnitaryAdditiveCharacter K)
    (D : supportedOn
      (upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w))),
    IsBiEquivariantDistribution ψ n (D : Distribution (GeneralLinear (n + 1) K)) →
    pushforward (weylTransposeHomeomorph n K)
      (D : Distribution (GeneralLinear (n + 1) K)) =
        -(D : Distribution (GeneralLinear (n + 1) K)) →
    ((∀ E : Distribution (UpperBruhatCell (n + 1) K w),
      IsBiEquivariantBruhatCellDistribution n K w ψ E → E = 0) ∨
      ∃ hτ : Set.MapsTo (weylTransposeHomeomorph n K)
        (upperBruhatCell (n + 1) K w) (upperBruhatCell (n + 1) K w),
        ∀ E : Distribution (UpperBruhatCell (n + 1) K w),
          IsBiEquivariantBruhatCellDistribution n K w ψ E →
            IsWeylTransposeInvariantBruhatCellDistribution n K w hτ E) →
    restrictOpen (isOpen_upperBruhatCellNeighborhood w)
      (D : Distribution (GeneralLinear (n + 1) K)) = 0

end Langlands.Whittaker
