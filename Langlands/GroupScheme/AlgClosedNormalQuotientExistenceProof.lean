import Langlands.GroupScheme.NormalQuotientExistenceReduction
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.AffineHomImageProof

/-! # Affine normal quotients over algebraically closed fields -/

universe u

namespace Langlands.GroupScheme

/-- The exact published proposition, with its structural inputs discharged. -/
theorem algClosedNormalQuotientExistence :
    AlgClosedNormalQuotientExistenceStatement.{u} :=
  algClosed_normalQuotientExistence_with_structural_inputs affineCartierSmooth affineHomImage

end Langlands.GroupScheme
