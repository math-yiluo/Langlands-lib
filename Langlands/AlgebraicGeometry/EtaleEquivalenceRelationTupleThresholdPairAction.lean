import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleThresholdQuotient
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionQuotientRelation

/-! # The diagonal pair action and the actual tuple threshold relation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]
  (N p q : ℕ) (hpq : p ≤ q)

local notation "L" => E.tupleTailPresentation N p
local notation "H" => E.tupleTailPresentation N q
local notation "c" => E.tupleTailCrossCoverSource N p q hpq
local notation "v" => E.tupleTailCrossCoverTarget N p q hpq
local notation "A" => E.tupleTailCrossCoverAction N p q hpq
local notation "a" => pullback.fst c c
local notation "b" => pullback.snd c c
local notation "k" => a ≫ c

/-- The actual diagonal action on the pair scheme of the tuple cross cover. -/
abbrev tupleTailCrossCoverDiagonalAction : Action H k := (A).pairAction

local notation "A₂" => E.tupleTailCrossCoverDiagonalAction N p q hpq

/-- The diagonal action preserves the first lower-tail target. -/
@[reassoc]
theorem tupleTailCrossCoverDiagonalAction_fst_target :
    (A₂).map ≫ a ≫ v = pullback.snd (H).s k ≫ a ≫ v := by
  change (A).pairMap ≫ a ≫ v = _
  rw [Action.pairMap_fst_assoc]
  simp only [Action.act, Category.assoc, E.tupleTailCrossCoverAction_target,
    pullback.lift_snd_assoc]

/-- The diagonal action preserves the second lower-tail target. -/
@[reassoc]
theorem tupleTailCrossCoverDiagonalAction_snd_target :
    (A₂).map ≫ b ≫ v = pullback.snd (H).s k ≫ b ≫ v := by
  change (A).pairMap ≫ b ≫ v = _
  rw [Action.pairMap_snd_assoc]
  simp only [Action.act, Category.assoc, E.tupleTailCrossCoverAction_target,
    pullback.lift_snd_assoc]

/-- A finite invariant affine quotient cover for the actual diagonal action. -/
def tupleTailCrossCoverDiagonalActionAffineQuotientCover (hq : q < N + 1) :
    (A₂).relation.InvariantAffineQuotientCover :=
  E.tupleTailCrossCoverPairActionAffineQuotientCover N p q hpq A₂
    (E.tupleTailCrossCoverDiagonalAction_fst_target N p q hpq)
    (E.tupleTailCrossCoverDiagonalAction_snd_target N p q hpq) hq

/-- The actual threshold arrow scheme is the quotient of the diagonal pair action. -/
def tupleTailThresholdDiagonalSchemeQuotient (hq : q < N + 1) :
    (A₂).relation.SchemeQuotient :=
  E.tupleTailThresholdPairSchemeQuotient N p q hpq hq A₂
    (E.tupleTailCrossCoverDiagonalAction_fst_target N p q hpq)
    (E.tupleTailCrossCoverDiagonalAction_snd_target N p q hpq)

variable (hq : q < N + 1)

local notation "W" => E.tupleChartThresholdOpen
  (fun j : {j : Fin (N + 1) // p ≤ j.val} => Fin.val (Subtype.val j)) q
local notation "Q" => E.tupleTailThresholdSchemeQuotient N p q hpq hq
local notation "Q₂" => E.tupleTailThresholdDiagonalSchemeQuotient N p q hpq hq

/-- The quotient relation has exactly the source map of the threshold chart relation. -/
theorem tupleTailThreshold_quotientRelation_s :
    ((A).quotientRelation Q Q₂).s = Chart.s L (W).ι :=
  (A).quotientS_eq Q Q₂ (E.tupleTailThresholdPairCover_s N p q hpq hq)

/-- The quotient relation has exactly the target map of the threshold chart relation. -/
theorem tupleTailThreshold_quotientRelation_t :
    ((A).quotientRelation Q Q₂).t = Chart.t L (W).ι :=
  (A).quotientT_eq Q Q₂ (E.tupleTailThresholdPairCover_t N p q hpq hq)

/-- The identity on schemes compares the actual threshold relation cartesianly
to the quotient relation of the actual cross-cover action. -/
theorem tupleTailThreshold_quotientRelation_isCartesianHom :
    IsCartesianHom ((L).chart (W).ι) ((A).quotientRelation Q Q₂)
      (𝟙 (W).toScheme) (𝟙 (Chart.arrows L (W).ι)) := by
  refine ⟨?_, ?_⟩
  · change (𝟙 (Chart.arrows L (W).ι)) ≫ (A).quotientT Q Q₂ =
      Chart.t L (W).ι ≫ (𝟙 (W).toScheme)
    rw [Category.id_comp, Category.comp_id]
    exact (A).quotientT_eq Q Q₂ (E.tupleTailThresholdPairCover_t N p q hpq hq)
  · change IsPullback (𝟙 (Chart.arrows L (W).ι)) (Chart.s L (W).ι)
      (((A).quotientRelation Q Q₂).s) (𝟙 (W).toScheme)
    rw [E.tupleTailThreshold_quotientRelation_s N p q hpq hq]
    exact IsPullback.of_id_fst

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
