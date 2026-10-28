import Langlands.Group.GL.UpperBruhatCells

/-!
# Actual upper Bruhat cell coordinate homeomorphisms

This module states the proposition only. See the paired Markdown for the
conventions, topologies and provenance.
-/

namespace Langlands.GeneralLinear

universe u

/-- Over every Hausdorff topological field, in every rank including zero and for every
permutation `w`, the published map `(b, v) ↦ b * p * v` underlies a homeomorphism
`B × U_w⁻ ≃ₜ C_w`, and `(u, d, v) ↦ u * p * diagonalUnits d * v` underlies a
homeomorphism `U × (Fin n → Kˣ) × U_w⁻ ≃ₜ C_w`, where `p = permutation n K w`. -/
def UpperBruhatCoordinatesStatement : Prop :=
  ∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
    (∃ eB : (upperTriangularSubgroup n K × permutationUnipotentMinus n K w) ≃ₜ
        UpperBruhatCell n K w,
      ∀ x, eB x = upperBruhatCellMap n K w x) ∧
    ∃ eT : (upperUnipotent n K × (Fin n → Kˣ) × permutationUnipotentMinus n K w) ≃ₜ
        UpperBruhatCell n K w,
      ∀ x, (eT x).val =
        x.1.val * permutation n K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val

end Langlands.GeneralLinear
