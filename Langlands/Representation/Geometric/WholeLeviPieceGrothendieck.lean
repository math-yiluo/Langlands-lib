import Langlands.Representation.Geometric.PieceGrothendieck
import Langlands.Representation.Geometric.WholeLeviPieceTransport
import Langlands.Representation.Geometric.FlattenedGrothendieckTransport
import Langlands.Representation.CuspidalSupport.LeviGrothendieckTransport
import Langlands.Representation.Aubert.RefinedAlternatingOperator

/-! Whole-target geometric pieces on the full exact finite-length K0. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear SmoothRep CuspidalSupport Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B)
  (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S) C w)

/-- The whole-target piece in actual flattened coordinates: normalized refined
Jacquet restriction, coordinate pullback, then inverse Levi conjugation. -/
def wholeLeviGeometricPieceK0 :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      C.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (leviTransportK0.{uF, uV} F.Carrier (B.flatten S) C w hw).toLinearMap.comp
    ((flattenedLeviK0.{uF, uV} F.Carrier B S).toLinearMap.comp
      (normalizedRefinedJacquetK0.{uF, uV} F T B S))

set_option maxHeartbeats 400000 in
/-- Whenever the flattened source is conjugate to the whole target, the actual
geometric-piece map equals the coordinate formula on every virtual class. -/
theorem geometricPieceK0_eq_wholeLevi
    (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    geometricPieceK0.{uF, uV} F T B C w S R hS hR =
      wholeLeviGeometricPieceK0.{uF, uV} F T B C w S hw := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object ℂ (B.Levi F.Carrier)
  intro A
  let J := (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A.val
  let D := SmoothRep.pullback (flattenedLeviEquivContinuous F.Carrier B S) J
  let Q := (transportFunctor (B.flatten S) C w hw).obj D
  let P := (geometricPieceSmoothFunctor.{uF, max uF uV}
    F T B C w S R hS hR).obj A.val
  have hJ : J.HasFiniteLength :=
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).2.1
      n B S A.val A.property
  have hD : D.HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength
      (flattenedLeviEquivContinuous F.Carrier B S) J hJ
  have hQ : Q.HasFiniteLength :=
    transportFunctor_preservesFiniteLength F.Carrier (B.flatten S) C w hw D hD
  have hP : P.HasFiniteLength :=
    geometricPieceSmoothFunctor_preservesFiniteLength.{uF, max uF uV}
      F T B C w S R hS hR A.val A.property
  change geometricPieceK0 F T B C w S R hS hR
      (B.finiteLengthClass F.Carrier A.val A.property) =
    leviTransportK0 F.Carrier (B.flatten S) C w hw
      (flattenedLeviK0 F.Carrier B S
        (normalizedRefinedJacquetK0 F T B S
          (B.finiteLengthClass F.Carrier A.val A.property)))
  have hPQ : C.finiteLengthClass F.Carrier P hP =
      C.finiteLengthClass F.Carrier Q hQ := by
    apply SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
    change P.obj.ρ.Equiv Q.representation
    dsimp only [P]
    rw [geometricPieceSmoothFunctor_obj_toRep F T B C w S R hS hR A.val]
    exact wholeLeviGeometricPieceEquiv.{uF, max uF uV}
      T B C w S R hS hR hw A.val
  have h0 := geometricPieceK0_finiteLengthClass.{uF, uV} F T B C w S R hS hR
    A.val A.property hP
  have h1 := leviTransportK0_finiteLengthClass.{uF, uV}
    F.Carrier (B.flatten S) C w hw D hD hQ
  have h2 := flattenedLeviK0_finiteLengthClass.{uF, uV} F.Carrier B S J hJ hD
  have h3 := normalizedRefinedJacquetK0_finiteLengthClass.{uF, uV}
    F T B S A.val A.property hJ
  have h4 := congrArg (leviTransportK0.{uF, uV} F.Carrier (B.flatten S) C w hw)
    h2.symm
  have h5 := congrArg (fun x => leviTransportK0.{uF, uV}
    F.Carrier (B.flatten S) C w hw (flattenedLeviK0.{uF, uV} F.Carrier B S x))
    h3.symm
  exact h0.trans (hPQ.trans (h1.symm.trans (h4.trans h5)))

end Langlands.Geometric
