import Langlands.Representation.Archimedean.ComplexUnitaryGenericExponentBoundProof
import Langlands.Representation.Archimedean.ComplexUnitaryGenericPairRegularityReductionProof
import Langlands.Representation.Archimedean.ComplexPairLFactorRegularityProof

/-!
# Getz–Hahn, Theorem 11.5.2, complex case

A proof of `Langlands.Archimedean.ComplexUnitaryGenericPairRegularityStatement`: the
published reduction applied to the published exponent bound at both carrier universes and to
the published right half-plane regularity of complex pair `L`-factors. See the paired
Markdown.
-/

set_option autoImplicit false

universe uV uW

namespace Langlands.Archimedean

/-- **Getz–Hahn 2024, Theorem 11.5.2, case `F = ℂ`.** For irreducible admissible generic
unitarizable `(𝔤𝔩_n(ℂ), U(n))`- and `(𝔤𝔩_m(ℂ), U(m))`-modules with standard parameters `ds`
and `ds'`, the denominator of `complexPairLFactor ds ds'` does not vanish when `1 ≤ Re(s)`. -/
theorem complexUnitaryGenericPairRegularity :
    ComplexUnitaryGenericPairRegularityStatement.{uV, uW} :=
  complexUnitaryGenericPairRegularityReduction.{uV, uW}
    complexUnitaryGenericExponentBound.{uV} complexUnitaryGenericExponentBound.{uW}
    complexPairLFactorRightHalfPlaneRegularity

end Langlands.Archimedean
