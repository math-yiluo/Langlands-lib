import Langlands.Representation.Classification.InductionWeakJacquetBoundsAssembly
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! Weak upper Jacquet bounds are preserved by actual normalized GL induction. -/

noncomputable section

namespace Langlands

universe uF uV

/-- Actual normalized induction from a standard Levi preserves the weak upper
bounds on standard Jacquet exponents. -/
theorem glInductionWeakJacquetBounds : GLInductionWeakJacquetBoundsStatement.{uF, uV} :=
  glInductionWeakJacquetBounds_of_geometricLemma Geometric.padicGeometricLemma.{uF, uV}

end Langlands
