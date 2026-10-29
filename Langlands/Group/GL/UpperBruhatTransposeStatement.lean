import Langlands.Group.GL.UpperBruhatFiltration
import Langlands.HarmonicAnalysis.Distribution.GeneralLinear

/-!
# Weyl-conjugated transpose of actual upper Bruhat cells and inversion layers

A proposition definition stating that the transpose index preserves the inversion
count, and that the published Weyl-conjugated transpose `g ↦ weylLong * gᵀ * weylLong`
maps the actual upper Bruhat cells, inversion layers, higher-cell unions and cell
neighborhoods as indexed by the transpose index. It contains no proof.
-/

namespace Langlands.GeneralLinear

universe u

/-- The transpose index `Fin.revPerm * w⁻¹ * Fin.revPerm` preserves the inversion
count in every rank, and, over every commutative topological ring, the published
homeomorphism `g ↦ weylLong * gᵀ * weylLong` maps the actual cell, higher-cell
union and cell neighborhood of `w` onto those of the transpose index, and maps every
inversion layer onto itself. -/
def UpperBruhatTransposeStatement : Prop :=
  (∀ (n : ℕ) (w : Equiv.Perm (Fin n)),
    permutationInversionCount n (upperBruhatTransposeIndex n w) =
      permutationInversionCount n w) ∧
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (n : ℕ) (w : Equiv.Perm (Fin n)) (k : ℕ),
    let tau : Langlands.GeneralLinear n R ≃ₜ Langlands.GeneralLinear n R :=
      (Langlands.HarmonicAnalysis.Distribution.transposeHomeomorph n R).trans
        (Langlands.HarmonicAnalysis.Distribution.conjugationHomeomorph
          (weylLong n R))
    tau '' upperBruhatCell n R w =
        upperBruhatCell n R (upperBruhatTransposeIndex n w) ∧
      tau '' upperBruhatLayerLE n R k = upperBruhatLayerLE n R k ∧
      tau '' upperBruhatHigherCells n R w =
        upperBruhatHigherCells n R (upperBruhatTransposeIndex n w) ∧
      tau '' upperBruhatCellNeighborhood n R w =
        upperBruhatCellNeighborhood n R (upperBruhatTransposeIndex n w)

end Langlands.GeneralLinear
