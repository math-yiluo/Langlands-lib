import Langlands.Representation.Aubert.General.RationalCuspidalExtractionFromSpecialVertex
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Actual rational cuspidal Jacquet-factor extraction: proof -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Renard VI.5.3(ii),(iii) after exact Jacquet restriction, for the actual
standard rational-point families: an irreducible inside-Levi cuspidal
subquotient of `r_J π`, for an arbitrary smooth subquotient `π` of
`i_I σ` with `σ` irreducible inside-Levi cuspidal, is isomorphic to the
transport of `σ` by one rational point `n` whose conjugation carries `M_J` to
`M_I` and which satisfies the root association. The joint special-compact
basis existence supplies the one structural input of the reduction. -/
theorem rationalCuspidalJacquetFactorExtraction :
    RationalCuspidalJacquetFactorExtractionStatement.{u, v} :=
  rationalCuspidalJacquetFactorExtraction_of_jointBasis
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.Aubert.General.RationalPointFamily
