import Langlands.Representation.Archimedean.RealUnitaryGenericExponentBoundProof
import Langlands.Representation.Archimedean.RealUnitaryGenericPairRegularityReductionProof
import Langlands.Representation.Archimedean.RealPairLFactorRegularityProof

/-!
# Getz–Hahn, Theorem 11.5.2, real case

A proof of `Langlands.Archimedean.RealUnitaryGenericPairRegularityStatement`: the Library's
reduction applied to the exponent bound `realUnitaryGenericExponentBound` at both carrier
universes and to the right half-plane regularity of real pair `L`-factors. See the paired
Markdown.
-/

universe uV uW

namespace Langlands.Archimedean

/-- **Getz–Hahn 2024, Theorem 11.5.2, case `F = ℝ`.** For irreducible admissible generic
unitarizable `(𝔤𝔩_n(ℝ), O(n))`- and `(𝔤𝔩_m(ℝ), O(m))`-modules with standard parameters `ds`
and `ds'`, the denominator of `realPairLFactor ds ds'` does not vanish when `1 ≤ Re(s)`. -/
theorem realUnitaryGenericPairRegularity :
    RealUnitaryGenericPairRegularityStatement.{uV, uW} :=
  realUnitaryGenericPairRegularityReduction.{uV, uW}
    realUnitaryGenericExponentBound.{uV} realUnitaryGenericExponentBound.{uW}
    realPairLFactorRightHalfPlaneRegularity

end Langlands.Archimedean
