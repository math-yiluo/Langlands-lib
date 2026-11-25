import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionBracketMapReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingProof

/-!
# Torsion bracket maps with finitely many configurations in each geometric fibre

A proof of `Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionBracketMapStatement`: the
Library's proved definition `torsionBracketMap_of_cubicFieldEmbedding` (torsion bracket maps from
Lefschetz's theorem over fields) applied to the cubic Lefschetz embedding `cubicFieldEmbedding`
at universe `0`. See the paired Markdown.
-/

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- **Torsion bracket maps.** For positive dimension and polarization index and every
sufficiently large level `n`, every datum over a level base `T` admits a morphism `j` from `T` to
a finite projective space over `Spec ℤ[1/n]` such that the `K`-points of `T` in each geometric
fibre of `j` carry only finitely many classes of torsion configurations. -/
theorem torsionBracketMap : TorsionBracketMapStatement :=
  torsionBracketMap_of_cubicFieldEmbedding cubicFieldEmbedding.{0}

end Langlands.AbelianScheme.PolarizedFiniteLevel
