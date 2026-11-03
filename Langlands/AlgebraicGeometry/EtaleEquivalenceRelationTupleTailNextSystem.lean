import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationStableActionQuotientSystem
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleThresholdPairAction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationFirstLevelInduction

/-! # Finite type systems on the actual next tuple threshold -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

/-- A first level of the higher tail gives a finite type cartesian system on
the actual next-threshold restriction, including the final empty threshold. -/
lemma nonempty_finiteTypeCartesianSystem_tupleTailNext (N p : ℕ)
    (hN : E.tupleLengthBound ≤ N) (_hp : p < N + 1)
    (M : AffineFiniteTypeFirstLevel (E.tupleTailPresentation N (p + 1))) :
    Nonempty (FiniteTypeCartesianSystem (E.tupleTailNextRelation N p)) := by
  by_cases hq : p + 1 < N + 1
  · let A := E.tupleTailCrossCoverAction N p (p + 1) (Nat.le_succ p)
    let Q := E.tupleTailThresholdSchemeQuotient N p (p + 1) (Nat.le_succ p) hq
    let Q₂ := E.tupleTailThresholdDiagonalSchemeQuotient N p (p + 1)
      (Nat.le_succ p) hq
    let φ : E.tupleTailNextRelation N p ⟶ A.quotientRelation Q Q₂ :=
      { objMap := 𝟙 _
        relMap := 𝟙 _
        isCartesian := E.tupleTailThreshold_quotientRelation_isCartesianHom
          N p (p + 1) (Nat.le_succ p) hq }
    let : IsIso φ.objMap := inferInstanceAs (IsIso (𝟙 _))
    exact ⟨M.actionQuotientSystem
      (E.tupleTailCrossCoverSource N p (p + 1) (Nat.le_succ p)) A
      (E.tupleTailCrossCoverAffineQuotientCover N p (p + 1) (Nat.le_succ p) hq)
      (E.tupleTailCrossCoverDiagonalActionAffineQuotientCover N p (p + 1)
        (Nat.le_succ p) hq)
      Q Q₂ φ⟩
  · have hW : E.tupleTailNextOpen N p = ⊥ :=
      E.tupleChartThresholdOpen_eq_bot _ (p + 1) (by omega)
    let : IsEmpty (E.tupleTailNextRelation N p).U := by
      change IsEmpty (E.tupleTailNextOpen N p).toScheme
      refine ⟨fun x => ?_⟩
      have hx : x.val ∈ E.tupleTailNextOpen N p := x.property
      simpa only [hW, TopologicalSpace.Opens.mem_bot] using hx
    exact ⟨(affineFiniteTypeFirstLevel_of_isEmpty _).system⟩

/-- Choose the finite type cartesian system furnished by the actual tuple-tail
step from a first level of the higher tail. -/
def tupleTailNextSystem (N p : ℕ)
    (hN : E.tupleLengthBound ≤ N) (hp : p < N + 1)
    (M : AffineFiniteTypeFirstLevel (E.tupleTailPresentation N (p + 1))) :
    FiniteTypeCartesianSystem (E.tupleTailNextRelation N p) :=
  Classical.choice (E.nonempty_finiteTypeCartesianSystem_tupleTailNext N p hN hp M)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
