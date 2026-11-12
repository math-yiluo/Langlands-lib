import Langlands.Representation.Plancherel.RationalSmoothRealDescentConstruction
import Langlands.BruhatTits.RationalPoints.CentralNormKernelCompactnessProof
import Langlands.BruhatTits.RationalPoints.CentralDerivedNormKernelCocompactnessProof
import Langlands.BruhatTits.RationalPoints.DerivedSmoothRealAnnihilationProof

/-! # Smooth real descent on actual reductive rational points

Proof of `RationalSmoothRealDescentStatement` (Renard V.3.19). The published conditional
reduction `rationalSmoothRealDescent_of_structure` has the three local-point structural
statements of `SmoothRealStructureStatement` as its only premise. The published proofs
`centralNormKernelCompactness`, `centralDerivedNormKernelCocompactness` and
`derivedSmoothRealAnnihilation` prove them. -/

universe u

namespace Langlands.Plancherel

open Langlands.BruhatTits.RationalPoints

/-- **Smooth real descent.** For every nonarchimedean local field `F` and every connected
reductive group `M` over `F`, every group homomorphism from the rational points to
`Multiplicative ℝ` whose kernel is open in the canonical rational-point topology kills the
common norm kernel, and factors uniquely through the valuation-image projection as a real
additive functional. -/
theorem rationalSmoothRealDescent : RationalSmoothRealDescentStatement.{u} :=
  rationalSmoothRealDescent_of_structure
    ⟨centralNormKernelCompactness.{u}, centralDerivedNormKernelCocompactness.{u},
      derivedSmoothRealAnnihilation.{u}⟩

end Langlands.Plancherel
