import Langlands.Representation.Exponents.SupportedRegularWeylParameterNumericsStatement
import Langlands.Representation.Exponents.SupportedRegularWeylParameterCones

/-! The finite-coordinate unit for the supported regular Weyl comparison. -/

namespace Langlands.Exponents

open SupportedRegularWeylComparison

/-- Weighted diagonal lifting and two independent one-sided comparisons
give the numerical conclusions with the first permutation. -/
theorem supportedRegularWeylParameterNumerics :
    SupportedRegularWeylParameterNumericsStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n B v hv
    exact diagonal_cone_of_weighted_block_cone B v hv
  · intro n B Q R S h v t hv
    exact ⟨closedCone_of_transported_positiveRootParameter B Q R S h v hv,
      orthogonality_of_positiveRootParameter B Q R S h v hv t,
      fun ht => antitone_coarseParameter B t ht⟩
  · intro n V1 V2 A1 A2 s r horth1 horth2 hanti1 hanti2 hcone1 hcone2 hrel1 hrel2 hV1
    exact ⟨transported_eq_of_two_oneSided_cones V1 V2 A1 A2 s r
        horth1 horth2 hanti1 hanti2 hcone1 hcone2 hrel1 hrel2,
      inverse_cone_of_two_oneSided_cones V1 V2 A1 A2 s r
        horth1 horth2 hanti1 hanti2 hcone1 hcone2 hrel1 hrel2 hV1⟩

end Langlands.Exponents
