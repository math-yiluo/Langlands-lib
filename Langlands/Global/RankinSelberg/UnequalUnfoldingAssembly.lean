import Langlands.Global.RankinSelberg.DualProjectionExpansionReduction
import Langlands.Global.RankinSelberg.ProjectionExpansionReduction
import Langlands.Global.RankinSelberg.UnequalUnfoldingGaugeStatement
import Langlands.Global.RankinSelberg.UnequalUnfoldingReduction
import Langlands.Global.RankinSelberg.CuspidalWhittakerExpansionProof
import Langlands.Global.RankinSelberg.DualWhittakerExpansionProof
import Langlands.Global.RankinSelberg.RectangleModulusProof
import Langlands.Global.RankinSelberg.UnequalGaugeReduction

/-! # Assembly of the unequal-rank unfolding: only the gauge premises remain

The published reduction `UnequalUnfoldingReductionStatement` derives `UnequalUnfoldingStatement`
from four premises E, E', G, G' for every pair. Here E and E' are discharged by the published
expansion reductions together with the published proofs of their hypotheses. What remains is
the gauge statement `UnequalUnfoldingGaugeStatement` (G and G' for every pair).
-/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The unequal-rank unfolding follows from the Whittaker expansion of cusp forms, the Whittaker
expansion of dual cusp forms with locally uniform convergence, the modulus of right
multiplication on adelic rectangles, and the gauge premises. -/
theorem unequalUnfolding_of_premises
    (hCWE : CuspidalWhittakerExpansionStatement.{u})
    (hDual : DualCuspidalWhittakerExpansionStatement.{u})
    (hJ : RectangleMeasureModulusStatement.{u})
    (hG : UnequalUnfoldingGaugeStatement.{u}) :
    UnequalUnfoldingStatement.{u} :=
  unequalUnfoldingReduction fun F _ _ _ r t h T T' =>
    ⟨projectionExpansionReduction F r t h T (hCWE F r T),
      dualProjectionExpansionReduction hJ F r t h T (hDual F r T),
      hG.1 F r t h T T', hG.2 F r t h T T'⟩

/-- The gauge premises `UnequalUnfoldingGaugeStatement` (G and G' for every actual positive
unequal-rank cuspidal pair) imply the unequal-rank unfolding `UnequalUnfoldingStatement`. -/
def UnequalUnfoldingGaugeSufficiencyStatement : Prop :=
  UnequalUnfoldingGaugeStatement.{u} → UnequalUnfoldingStatement.{u}

/-- Proof of `UnequalUnfoldingGaugeSufficiencyStatement` from the published proofs of the
expansion and modulus statements. -/
theorem unequalUnfoldingGaugeSufficiency : UnequalUnfoldingGaugeSufficiencyStatement.{u} :=
  fun hG => unequalUnfolding_of_premises cuspidalWhittakerExpansionStatement_proof
    dualCuspidalWhittakerExpansionStatement_proof rectangleMeasureModulus hG

/-- With the published conditional gauge reduction, the two Whittaker gauge bounds
`UnequalPadGaugeStatement` and `UnequalRectGaugeStatement` imply the unequal-rank unfolding. -/
theorem unequalUnfolding_of_whittakerGauges (hPad : UnequalPadGaugeStatement.{u})
    (hRect : UnequalRectGaugeStatement.{u}) :
    UnequalUnfoldingStatement.{u} :=
  unequalUnfoldingGaugeSufficiency (unequalGaugeReduction hPad hRect)

end Langlands.Global.RankinSelbergGlobal
