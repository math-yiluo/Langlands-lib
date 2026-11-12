import Langlands.Topology.LocallyProfinite
import Mathlib.Topology.Algebra.MulAction

/-! # Renard II.3.3: an orbit quotient need not be Hausdorff -/

set_option autoImplicit false

namespace Langlands.Topology.RenardOrbitQuotient

/-- The non-Hausdorff warning in the paragraph before the II.3.3 Lemma,
expressed on actual continuous actions and their quotient topology. -/
def NonHausdorffOrbitQuotientStatement : Prop :=
  ∃ (G X : Type) (groupG : Group G)
    (topologyG : TopologicalSpace G) (topologyX : TopologicalSpace X),
    letI : Group G := groupG
    letI : TopologicalSpace G := topologyG
    letI : TopologicalSpace X := topologyX
    ∃ action : MulAction G X,
      letI : MulAction G X := action
      IsTopologicalGroup G ∧ ContinuousSMul G X ∧
        IsLocallyProfinite G ∧ IsLocallyProfinite X ∧
        ¬ T2Space (Quotient (MulAction.orbitRel G X))

end Langlands.Topology.RenardOrbitQuotient
