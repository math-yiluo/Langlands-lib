import Langlands.Representation.RankinSelberg.GammaNormalizationStatement
import Langlands.Representation.RankinSelberg.GammaNormalizationAlgebra

/-! Proof of the published algebraic normalization statement from the
normalization theorem of `GammaNormalizationAlgebra`. -/

namespace Langlands.RankinSelberg

/-- The two incidence hypotheses and normalized generators give one nonzero
monomial for every rational pair satisfying the gamma equation. -/
theorem gammaNormalization : GammaNormalizationStatement :=
  fun _q hq ζ e G S T P Pdual hP hPd hST hTS =>
    gammaNormalization_of_incidence hq ζ e G S T P Pdual hP hPd hST hTS

end Langlands.RankinSelberg
