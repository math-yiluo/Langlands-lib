import Langlands.AbelianScheme.PolarizedFiniteLevel.ModuliZariskiSheafOfRigidityProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingProof

/-!
# The ordinary polarized full-level moduli functor is a Zariski sheaf for large levels

A proof of `Langlands.AbelianScheme.PolarizedFiniteLevel.EventualModuliZariskiSheafStatement`:
the Library's proved definition `eventualModuliZariskiSheaf_of_cubicFieldEmbedding` (Lefschetz's
theorem over fields implies the eventual Zariski sheaf property) applied to the cubic Lefschetz
embedding `cubicFieldEmbedding` at universe `0`. See the paired Markdown.
-/

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- **The eventual Zariski sheaf property.** For positive dimension and polarization index there
is a bound `N` such that, for every level `n ≥ max N 3`, the ordinary polarized full-level
moduli functor satisfies the Zariski sheaf condition on the level base category. -/
theorem eventualModuliZariskiSheaf : EventualModuliZariskiSheafStatement :=
  eventualModuliZariskiSheaf_of_cubicFieldEmbedding cubicFieldEmbedding.{0}

end Langlands.AbelianScheme.PolarizedFiniteLevel
