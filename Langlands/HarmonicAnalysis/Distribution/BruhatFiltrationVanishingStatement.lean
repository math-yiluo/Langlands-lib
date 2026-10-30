import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Langlands.HarmonicAnalysis.Distribution.Subspace

/-!
# Vanishing from open restrictions along the finite upper Bruhat filtration

An internally derived support-removal statement for algebraic distributions on `GL_n(K)`,
indexed by the actual upper Bruhat cells and their inversion counts. See the paired Markdown.
-/

namespace Langlands.HarmonicAnalysis.Distribution

open GeneralLinear

universe u

/-- If, for every permutation `w`, support of `D` on the closed layer of cells with at most
as many inversions as `w` forces the open restriction of `D` to the neighborhood of the cell
of `w` to vanish, then `D = 0`. -/
def BruhatFiltrationVanishingStatement : Prop :=
  ∀ (n : ℕ) (K : Type u) [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K]
    [LocallyCompactSpace (GeneralLinear n K)]
    [TotallyDisconnectedSpace (GeneralLinear n K)]
    (D : Distribution (GeneralLinear n K)),
    (∀ w : Equiv.Perm (Fin n),
      D ∈ supportedOn (upperBruhatLayerLE n K (permutationInversionCount n w)) →
        restrictOpen (isOpen_upperBruhatCellNeighborhood w) D = 0) →
    D = 0

end Langlands.HarmonicAnalysis.Distribution
