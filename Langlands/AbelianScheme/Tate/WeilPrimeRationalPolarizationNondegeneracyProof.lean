import Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyReduction
import Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyFromField
import Langlands.AbelianScheme.AlgClosedPointDivisibility
import Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveProof

/-! # Nondegeneracy of the rational prime-adic polarization Weil pairing -/

universe u

set_option autoImplicit false

namespace Langlands.AbelianScheme

/-- The rational prime-adic polarization Weil pairing is nondegenerate at every
algebraically closed geometric point whose characteristic is different from `p`. -/
theorem primeRationalPolarizationWeilNondegeneracy :
    PrimeRationalPolarizationWeilNondegeneracyStatement.{u} :=
  primeRationalPolarizationWeilNondegeneracyReduction
    (geometricFiniteWeilNondegeneracy_of_fieldDualKernelCharacterBijective
      fieldDualKernelCharacterBijective)
    algClosedPointDivisibility

end Langlands.AbelianScheme
