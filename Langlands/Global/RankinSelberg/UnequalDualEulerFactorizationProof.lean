import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationUnfoldingReduction
import Langlands.Global.RankinSelberg.UnequalUnfoldingAssembly
import Langlands.Global.RankinSelberg.UnequalPadGaugeProof
import Langlands.Global.RankinSelberg.UnequalRectGaugeOfSimpleRootGauge
import Langlands.Global.RankinSelberg.WhittakerSimpleRootMajorization
import Langlands.Global.RankinSelberg.RectangularGaugeMellinProof

/-! # Proof of the unequal-rank dual Euler factorization

The published reduction `unequalDualEulerFactorizationUnfoldingReduction` derives
`UnequalDualEulerFactorizationStatement` from `UnequalUnfoldingStatement`. The unfolding
statement follows from the published assembly `unequalUnfolding_of_whittakerGauges` and the
published proofs of its gauge inputs. See the paired Markdown.
-/

universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The unequal-rank unfolding, assembled from the published gauge proofs. -/
theorem unequalUnfolding_of_gaugeProofs : UnequalUnfoldingStatement.{u} :=
  unequalUnfolding_of_whittakerGauges unequalPadGauge
    (unequalRectGauge_of_simpleRootGauge whittakerSimpleRootMajorization
      adelicSimpleRootGaugeRectangularMellin)

/-- The partial Euler factorization of the unequal-rank dual global Whittaker integral
(Cogdell 2004, §§2.2, 4.1). -/
theorem unequalDualEulerFactorization : UnequalDualEulerFactorizationStatement.{u, uQ} :=
  UnequalDualEulerContragredient.unequalDualEulerFactorizationUnfoldingReduction
    unequalUnfolding_of_gaugeProofs

end Langlands.Global.RankinSelbergGlobal
