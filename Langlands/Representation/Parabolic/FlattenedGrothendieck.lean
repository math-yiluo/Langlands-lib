import Langlands.Representation.Parabolic.ComposedGrothendieck
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Geometric.FlattenedGrothendieckTransport

/-! Composed induction in actual flattened coordinates on exact K0. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Actual induction from the flattened block shape, after the literal
flattened coordinate change on exact finite-length K0. -/
def normalizedFlattenedInductionK0 :
    letI := T.topology
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F.Carrier B S) →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (normalizedInductionK0.{uF, uV} F T (B.flatten S)).comp
    (flattenedLeviK0.{uF, uV} F.Carrier B S).toLinearMap

/-- Direct composed induction and induction in flattened coordinates agree on
every virtual finite-length class, with the actual normalizing characters. -/
theorem normalizedComposedInductionK0_eq_flattened :
    letI := T.topology
    normalizedComposedInductionK0.{uF, uV} F T B S =
      normalizedFlattenedInductionK0.{uF, uV} F T B S := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object
    ℂ (refinedLevi F.Carrier B S)
  intro A
  let D := SmoothRep.pullback (flattenedLeviEquivContinuous F.Carrier B S) A.val
  let I := (T.normalizedParabolicInductionFunctor.{uF, max uF uV}
    (B.flatten S)).obj D
  let Q := (T.normalizedComposedInductionFunctor.{uF, max uF uV} B S).obj A.val
  have hD : D.HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength
      (flattenedLeviEquivContinuous F.Carrier B S) A.val A.property
  have hI : I.HasFiniteLength :=
    normalizedInductionK0_hasFiniteLength.{uF, uV} F T (B.flatten S) D hD
  have hQ : Q.HasFiniteLength :=
    normalizedComposedInduction_preservesFiniteLength.{uF, max uF uV}
      F T B S A.val A.property
  change normalizedComposedInductionK0 F T B S
      (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property) =
    normalizedInductionK0 F T (B.flatten S)
      (flattenedLeviK0 F.Carrier B S
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property))
  rw [normalizedComposedInductionK0_finiteLengthClass F T B S A.val A.property hQ,
    flattenedLeviK0_finiteLengthClass F.Carrier B S A.val A.property hD,
    normalizedInductionK0_finiteLengthClass F T (B.flatten S) D hD hI]
  apply SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
  exact (composedFlattenedInduction.{uF, max uF uV}
    p F T n B S A.val A.val.representation).choose

end Langlands.Parabolic
