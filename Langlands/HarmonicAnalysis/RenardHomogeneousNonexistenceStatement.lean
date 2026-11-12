import Langlands.Topology.LocallyProfinite
import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.Group.LeftQuotient

/-! # Renard II.3.9: untwisted invariant distributions need not exist -/

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard

/-- The initial warning of II.3.9, on the actual homogeneous quotient and
its actual right translations, in the source's positive-distribution language. -/
def NonexistenceStatement : Prop :=
  ∃ (G : Type) (groupG : Group G) (topologyG : TopologicalSpace G),
    letI : Group G := groupG
    letI : TopologicalSpace G := topologyG
    ∃ topologicalG : IsTopologicalGroup G,
      letI : IsTopologicalGroup G := topologicalG
      Langlands.Topology.IsLocallyProfinite G ∧
        ∃ H : Subgroup G, IsClosed (H : Set G) ∧
          ¬ ∃ T : Distribution (Langlands.Induction.LeftQuotient H),
            Distribution.IsPositive T ∧
              ∀ g : G,
                Distribution.pushforward (Langlands.QuotientIntegration.rightTranslate H g) T = T

end Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard
