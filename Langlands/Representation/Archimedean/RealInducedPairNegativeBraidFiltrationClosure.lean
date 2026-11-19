import Langlands.Representation.Archimedean.RealInducedPairNegativeBraidFiltration
import Langlands.Representation.Archimedean.RealCompactCharacterPolynomialBraid

/-! # Application of the full compact braid to the negative-inner case -/

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement

/-- The real two-block adjacent filtration in the linked negative-inner case. -/
theorem realInducedPairFiltration_of_negativeInner {d e : ComplexCharacterData} {k : ℕ}
    (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) :=
  RealInducedPairNegativeBraidFiltration.filtration hlink hneg
    RealCompactCharacterPolynomialBraid.polynomial_braid

end Langlands.Archimedean
