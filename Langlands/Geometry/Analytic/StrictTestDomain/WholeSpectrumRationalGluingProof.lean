import Langlands.Geometry.Analytic.StrictTestDomain.WholeSpectrumConditionalAssembly
import Langlands.Geometry.Analytic.StrictTestDomain.NontrivialStandardRationalGluingProof

/-! # Scalar rational descent over the whole spectrum -/

universe u

namespace Langlands.Analytic.StrictTestDomain

/-- Compatible scalar sections on a finite rational cover of the whole spectrum
uniquely descend along the actual rational quotient base maps. -/
theorem wholeSpectrumRationalGluing :
    WholeSpectrumRationalGluingStatement.{u} :=
  wholeSpectrumRationalGluing_of_nontrivial_standard
    nontrivialStandardRationalGluing

end Langlands.Analytic.StrictTestDomain
