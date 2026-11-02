import Langlands.Representation.Aubert.General.StandardExactness
import Langlands.Representation.Aubert.General.SupportCategory

/-! The corrected full-smooth Theorem 3.6 target on the actual normalized complex. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
variable (hclosed : ∀ J, IsClosed (U J : Set G))
variable (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
variable (hP : Monotone P) (hU : Antitone U)

/-- Corrected Theorem 3.6: every smooth object of `Alg({I})` is exact before the
retained terminal degree. Standard-subset endpoints identify degree zero with `E`. -/
def CorrectedTheorem36Statement
    (IsAssociate : Finset ι → Finset ι → G → Prop)
    (_hPtop : P Finset.univ = ⊤) (_hUtop : U Finset.univ = ⊥)
    (I : Finset ι) (hM : IsClosed (M I : Set G))
    (hI : ∀ K : Finset I,
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I))
        ((U (leviIndex I K)).subgroupOf (M I))) : Prop :=
  ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
    IsInSupportCategory P M U h hclosed IsAssociate I hM hI E →
      StandardComplex.IsExactBeforeTerminal P M U h hclosed hδ hP hU E I

end Langlands.Aubert.General
