import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundCech
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingProof

/-!
# The `H¹` dimension bound for abelian schemes over a field

For an abelian scheme `A` of relative dimension `g` over a field `k`, the `k`-module
`H¹(A, 𝒪_A)` is finite-dimensional of dimension at most `g`. The proof applies
`fieldStructureSheafH1DimensionBound_of_dim_of_vanishing` to the published proofs of the
topological dimension bound for quasi-compact smooth schemes over a field and of the vanishing
of quasi-coherent cohomology above the dimension of a noetherian separated scheme.
-/

universe u

namespace Langlands.AbelianScheme

/-- For an abelian scheme `A` of relative dimension `g` over a field `k`, `H¹(A, 𝒪_A)` is a
finite-dimensional `k`-vector space of dimension at most `g`. -/
theorem fieldStructureSheafH1DimensionBound : FieldStructureSheafH1DimensionBoundStatement.{u} :=
  fieldStructureSheafH1DimensionBound_of_dim_of_vanishing
    Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim
    Langlands.AlgebraicGeometry.Modules.noetherianSeparatedQuasicoherentVanishing

end Langlands.AbelianScheme
