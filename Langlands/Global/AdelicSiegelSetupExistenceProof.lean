import Langlands.Global.AdelicSiegelSetupExistence
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Derived.MaximalSplitTorusProof
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof

/-! # Existence of the actual algebraic Siegel setup -/

universe u

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme

/-- Every affine, locally finite type, connected reductive group scheme over a number
field admits the canonical algebraic Siegel setup. -/
theorem siegelAlgebraicSetupExistence : SiegelAlgebraicSetupExistenceStatement.{u} :=
  siegelAlgebraicSetupExistence_of_structural genericMinimalParabolic
    derivedMaximalSplitTorus derivedCentralSplitTorusProduct

end Langlands.Global.AdelicSiegelFactors
