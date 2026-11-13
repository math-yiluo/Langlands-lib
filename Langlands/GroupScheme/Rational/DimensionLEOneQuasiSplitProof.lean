import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction
import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRationalReduction
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotient

/-! # Steinberg's quasi-splitness theorem for fields of dimension at most one

The closing proof composes three published results: Steinberg's class quotient
`quasiSplitSteinbergQuotient`, the reduction `quasiSplitRegularClassRationalReduction` from the
class quotient to the rationality of Galois-stable strongly regular classes, and the assembly
`dimensionLEOneQuasiSplit_of_classRational` of quasi-splitness from that rationality. -/

universe u

namespace Langlands.GroupScheme

/-- **Steinberg's theorem** (Kaletha–Prasad 2023, Theorem 2.3.3(2)): over a field satisfying the
finite-separable/Galois unit-norm criterion for dimension at most one, every connected reductive
group scheme is quasi-split. -/
theorem dimensionLEOneQuasiSplit : DimensionLEOneQuasiSplitStatement.{u} :=
  dimensionLEOneQuasiSplit_of_classRational
    (quasiSplitRegularClassRationalReduction quasiSplitSteinbergQuotient)

end Langlands.GroupScheme
