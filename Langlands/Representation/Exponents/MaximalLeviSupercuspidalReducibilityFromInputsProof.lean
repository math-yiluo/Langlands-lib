import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityFromInputsStatement
import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryProof
import Langlands.Representation.Exponents.MaximalLeviReducibilityInductionInputs
import Langlands.Representation.Exponents.LeviInductionHermitianDualityReduction
import Langlands.Representation.Exponents.MaximalLeviUnitaryCentralTwistReduction

/-! # Proof of Renard VII.1.3 from its remaining inputs

The target follows from its unitary case and the unramified-twist step
(`maximalLeviSupercuspidalReducibility_of_unitary`). The twist step follows from
`ParabolicDynamicStatement`. The unitary case follows from the input statements of
`MaximalLeviReducibilityUnitaryInputs`, three of which concern induction alone and are
proved from compactness, unimodularity and root presentations, together with hermitian
duality.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- **Renard VII.1.3 from its remaining inputs.** -/
theorem maximalLeviSupercuspidalReducibilityFromInputs :
    MaximalLeviSupercuspidalReducibilityFromInputsStatement.{u, v} := by
  intro hPD hI0 hI0G hCompact hUnimod hStandard hPres hI1 hK1 hK2 hC
  exact maximalLeviSupercuspidalReducibility_of_unitary
    (maximalLeviSupercuspidalReducibilityUnitary_of_inputs hI0 hI0G hI1
      (leviInductionAdmissible_of_quotientCompact hCompact)
      (leviInductionUnitarizable_of_inputs hUnimod hStandard hCompact hPres)
      leviInductionNontrivial
      (leviInductionHermitianDuality_of_presentation hCompact hUnimod hStandard hPres)
      hK1 hK2 hC)
    (maximalLeviUnitaryCentralTwist_of_parabolicDynamic hPD)

end Langlands.Aubert.General.RepresentedParabolic
