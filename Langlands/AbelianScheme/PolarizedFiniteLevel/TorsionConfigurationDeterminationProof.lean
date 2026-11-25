import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationDeterminationReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundlePolarizationDeterminationProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingProof

/-!
# At large level, torsion configurations determine data over algebraically closed fields

A proof of
`Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationDeterminationStatement`: the
Library's proved definition `torsionConfigurationDetermination_of_cubicFieldEmbedding` applied to
the cubic Lefschetz embedding `cubicFieldEmbedding` and to the recovery of the polarization from
the cubic bundle `cubicBundlePolarizationDetermination`. See the paired Markdown.
-/

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- **Torsion configurations determine data at large level.** For positive dimension and
polarization index there is a bound `N` such that, for every level `n ≥ N` and every
algebraically closed field in which `n` is nonzero, two data over the field whose torsion
configurations are equivalent are isomorphic. -/
theorem torsionConfigurationDetermination : TorsionConfigurationDeterminationStatement.{u} :=
  torsionConfigurationDetermination_of_cubicFieldEmbedding cubicFieldEmbedding
    cubicBundlePolarizationDetermination

end Langlands.AbelianScheme.PolarizedFiniteLevel
