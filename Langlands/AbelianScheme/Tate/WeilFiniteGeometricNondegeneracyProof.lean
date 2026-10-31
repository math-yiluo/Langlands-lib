import Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyFromField
import Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveProof

/-! # Geometric-point nondegeneracy of the actual finite Weil pairing -/

universe u

namespace Langlands.AbelianScheme

/-- At a geometric point whose field has characteristic prime to `n`, the existing actual
finite Weil pairing `A[n] × A^t[n] → μ_n` on points has trivial left and right kernels. -/
theorem geometricFiniteWeilNondegeneracy : GeometricFiniteWeilNondegeneracyStatement.{u} :=
  geometricFiniteWeilNondegeneracy_of_fieldDualKernelCharacterBijective
    fieldDualKernelCharacterBijective

end Langlands.AbelianScheme
