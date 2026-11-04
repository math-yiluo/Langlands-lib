import Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularization
import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingReduction

/-! # The Lie–Kolchin closed embedding into the upper triangular group scheme -/

universe u

namespace Langlands.GroupScheme

/-- **Lie–Kolchin.** A smooth connected solvable affine group over an algebraically closed
field admits a closed embedding into the concrete upper triangular group scheme. -/
theorem solvableTriangularEmbeddingStatement : SolvableTriangularEmbeddingStatement.{u} :=
  solvableTriangularEmbedding_of_rationalTriangularization lieKolchinRationalTriangularization

end Langlands.GroupScheme
