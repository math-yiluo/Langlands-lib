import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets

/-! # Reductions of the Sharp class formula and of cuspidal-series retention

Two implication statements between published targets on the actual rational
points. Each one says that a main target of Aubert's Corollaire 3.9 follows
from named sibling targets. No proof is supplied here.
-/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Reduction of the signed class formula (Aubert 1995, Corollaire 3.9 (a),
extended to finite-length members of `Alg({I})` by the 1996 erratum) on the
actual rational-point families to four published support and graded targets:
vanishing of the non-standard graded pieces of the corrected support
filtration, stability of the actual support categories under the
induction-Jacquet composites, exactness detection on the actual support
categories, and vanishing of Jacquet modules along Levis not containing an
associate of the support. No proof is supplied. -/
def RationalSharpClassFormulaReductionStatement : Prop :=
  RationalCorrectedGradedVanishingStatement.{u, v} →
    RationalSupportCategoryInductionJacquetStatement.{u, v} →
      RationalSupportCategoryExactnessDetectionStatement.{u, v} →
        RationalSupportCategoryJacquetVanishingStatement.{u, v} →
          RationalSharpClassFormulaStatement.{u, v}

/-- Reduction of cuspidal-series retention by the actual terminal cokernel
(the derived step in the proof of Aubert 1995, Corollaire 3.9 (c)) to the two
sibling Sharp targets on the actual rational-point families: retention of the
support category by `E#` and irreducibility of `E#` on the cuspidal series.
No proof is supplied. -/
def RationalSharpCuspidalSeriesReductionStatement : Prop :=
  RationalSharpSupportRetentionStatement.{u, v} →
    RationalSharpIrreducibleStatement.{u, v} →
      RationalSharpCuspidalSeriesStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
