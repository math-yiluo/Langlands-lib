import Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyStatement
import Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyStatement
import Langlands.AbelianScheme.AlgClosedPointDivisibilityStatement

/-! # Reduction of rational prime-adic polarization nondegeneracy to finite levels -/

universe u

set_option autoImplicit false

namespace Langlands.AbelianScheme

/-- Finite-level nondegeneracy of the actual Weil pairing at geometric points, together
with divisibility of geometric points of abelian schemes, implies nondegeneracy of the
actual rational prime-adic polarization Weil pairing at geometric points. This is a
conditional statement target, not a proof of either hypothesis. -/
def PrimeRationalPolarizationWeilNondegeneracyReductionStatement : Prop :=
  GeometricFiniteWeilNondegeneracyStatement.{u} →
    AlgClosedPointDivisibilityStatement.{u} →
      PrimeRationalPolarizationWeilNondegeneracyStatement.{u}

end Langlands.AbelianScheme
