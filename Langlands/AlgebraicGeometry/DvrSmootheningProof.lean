import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Langlands.AlgebraicGeometry.BlowupChartProof
import Langlands.AlgebraicGeometry.DvrSmoothening.DefectBound
import Langlands.AlgebraicGeometry.DvrSmoothening.DefectZero
import Langlands.AlgebraicGeometry.DvrSmoothening.DilatationDefect
import Langlands.AlgebraicGeometry.DvrSmoothening.GoodChart
import Langlands.AlgebraicGeometry.DvrSmoothening.Reduction

/-! # Existence of smoothenings over discrete valuation rings -/

universe u

namespace Langlands.AlgebraicGeometry

/-- **Existence of smoothenings** (BLR §3.1, Theorem 3, in the form of §3.6, Lemma 5): every
quasi-compact scheme locally of finite type over a discrete valuation ring `R` with smooth generic
fibre has a proper morphism to it that is an isomorphism on generic fibres, through whose smooth
locus every point with values in a discrete valuation ring of ramification index one over `R`
lifts. -/
theorem dvrSmootheningStatement : DvrSmootheningStatement.{u} :=
  DvrSmoothening.dvrSmoothening_of DvrSmoothening.defectZeroSmoothAtStatement
    DvrSmoothening.dilatationDefectStatement DvrSmoothening.goodChartStatement
    DvrSmoothening.defectBoundStatement blowupChartStatement

end Langlands.AlgebraicGeometry
