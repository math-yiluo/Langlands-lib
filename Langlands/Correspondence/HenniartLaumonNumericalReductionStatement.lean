import Langlands.Correspondence.HenniartLadicStatement
import Langlands.Correspondence.HenniartLaumonNumericalStatement

/-!
# Reduction of Laumon's numerical statement E1b to the ℓ-adic statements

Henniart (1988), §4.3: Laumon's numerical rank shift `LaumonNumericalStatement` (E1b)
follows from the comparison of ℓ-adic and complex Weil unramified-twist orbit strata
(`LadicWeilOrbitComparisonStatement`) and Laumon's twist-equivariant bijection of ℓ-adic
Swan strata (`LaumonLadicTwistBijectionStatement`). This file states the implication and
does not prove it.
-/

namespace Langlands.Henniart

/-- **Reduction of E1b.** The comparison of ℓ-adic and complex Weil unramified-twist orbit
strata, with field and separable closure in universe `uK` and representation carriers in
universe `uW`, and Laumon's twist-equivariant bijection of ℓ-adic Swan strata over
`LaurentSeries k`, at the same universes, imply Laumon's numerical statement E1b: over
`LaurentSeries k` for a finite field `k`, the refined Weil strata of ranks `d + 1` and
`d + s + 1` with the same positive Swan exponent `s` and torsion number `f` have the same
extended cardinality. -/
def LaumonNumericalReductionStatement.{uK, uW} : Prop :=
  LadicWeilOrbitComparisonStatement.{uK, uK, uW} →
    LaumonLadicTwistBijectionStatement.{uK, uW} →
      LaumonNumericalStatement.{uK, uW}

end Langlands.Henniart
