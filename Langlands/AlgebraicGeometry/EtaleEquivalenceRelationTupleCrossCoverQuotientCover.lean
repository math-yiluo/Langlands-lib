import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossCoverKernelPair
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationQuotientOpenCover

/-! # Finite affine quotient charts for the tuple cross-cover action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]
  (N p q : ℕ) (hpq : p ≤ q)

instance tupleTailCrossCoverAction_object_isAffine :
    IsAffine (E.tupleTailCrossCoverAction N p q hpq).relation.U := by
  change IsAffine (E.tupleTailCrossCoverScheme N p q hpq)
  infer_instance

instance tupleTailCrossCoverAction_relation_isAffine :
    IsAffine (E.tupleTailCrossCoverAction N p q hpq).relation.R :=
  (E.tupleTailCrossCoverAction N p q hpq).isAffine_relation

/-- The actual cross-cover action has finitely many invariant affine open
charts, each with an affine scheme quotient. -/
def tupleTailCrossCoverAffineQuotientCover (hq : q < N + 1) :
    (E.tupleTailCrossCoverAction N p q hpq).relation.InvariantAffineQuotientCover := by
  exact @invariantAffineQuotientCoverOfCompactImage
    (E.tupleTailCrossCoverAction N p q hpq).relation
    (E.tupleTailPresentation N p).U
    (E.tupleTailCrossCoverTarget N p q hpq)
    (E.tupleTailCrossCoverAction_target_isPullback N p q hpq)
    inferInstance inferInstance (E.tupleTailCrossCoverTarget_etale N p q hpq)
    (E.tupleChartThresholdOpen
      (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val) q)
    (E.tupleChartThresholdOpen_isCompact
      (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val) q)
    (E.tupleTailCrossCoverTarget_range N p q hpq hq)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
