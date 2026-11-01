import Langlands.Representation.Parabolic.FlattenedGrothendieck
import Langlands.Representation.Parabolic.FlattenedJacquetComparisonProof

/-! Actual flattened Jacquet restriction and composed induction-Jacquet on exact K0. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Direct composed Jacquet restriction, followed by the actual flattened
coordinate pullback on exact finite-length K0. -/
def normalizedFlattenedJacquetK0 :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      (B.flatten S).FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (flattenedLeviK0.{uF, uV} F.Carrier B S).toLinearMap.comp
    (normalizedComposedJacquetK0.{uF, uV} F T B S)

/-- Composed restriction in actual flattened coordinates is the ordinary
normalized Jacquet map of the flattened block shape, on all virtual classes. -/
theorem normalizedFlattenedJacquetK0_eq :
    letI := T.topology
    normalizedFlattenedJacquetK0.{uF, uV} F T B S =
      normalizedJacquetK0.{uF, uV} F T (B.flatten S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object
    ℂ (GeneralLinear n F.Carrier)
  intro A
  let Q := (T.normalizedComposedJacquetFunctor.{uF, max uF uV} B S).obj A.val
  let D := SmoothRep.pullback (flattenedLeviEquivContinuous F.Carrier B S) Q
  let J := (T.normalizedJacquetFunctor.{uF, max uF uV} (B.flatten S)).obj A.val
  have hQ : Q.HasFiniteLength :=
    normalizedComposedJacquet_preservesFiniteLength.{uF, max uF uV}
      F T B S A.val A.property
  have hD : D.HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength
      (flattenedLeviEquivContinuous F.Carrier B S) Q hQ
  have hJ : J.HasFiniteLength :=
    normalizedJacquetK0_hasFiniteLength.{uF, uV} F T (B.flatten S) A.val A.property
  change flattenedLeviK0 F.Carrier B S
      (normalizedComposedJacquetK0 F T B S
        (GeneralLinear.finiteLengthClass n F.Carrier A.val A.property)) =
    normalizedJacquetK0 F T (B.flatten S)
      (GeneralLinear.finiteLengthClass n F.Carrier A.val A.property)
  rw [normalizedComposedJacquetK0_finiteLengthClass.{uF, uV}
      F T B S A.val A.property hQ,
    flattenedLeviK0_finiteLengthClass.{uF, uV} F.Carrier B S Q hQ hD,
    normalizedJacquetK0_finiteLengthClass.{uF, uV}
      F T (B.flatten S) A.val A.property hJ]
  apply SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
  exact (flattenedJacquetComparison.{uF, uF, max uF uV}).2
    F T B S A.val.representation |>.choose

/-- The nested induction-Jacquet term is the ordinary induction-Jacquet term
of the flattened shape, for every virtual class and every rank. -/
theorem normalizedComposedInductionK0_comp_composedJacquetK0 :
    letI := T.topology
    (normalizedComposedInductionK0.{uF, uV} F T B S).comp
        (normalizedComposedJacquetK0.{uF, uV} F T B S) =
      (normalizedInductionK0.{uF, uV} F T (B.flatten S)).comp
        (normalizedJacquetK0.{uF, uV} F T (B.flatten S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [normalizedComposedInductionK0_eq_flattened.{uF, uV} F T B S]
  change ((normalizedInductionK0.{uF, uV} F T (B.flatten S)).comp
      (flattenedLeviK0.{uF, uV} F.Carrier B S).toLinearMap).comp
        (normalizedComposedJacquetK0.{uF, uV} F T B S) = _
  rw [LinearMap.comp_assoc]
  change (normalizedInductionK0.{uF, uV} F T (B.flatten S)).comp
    (normalizedFlattenedJacquetK0.{uF, uV} F T B S) = _
  rw [normalizedFlattenedJacquetK0_eq.{uF, uV} F T B S]

end Langlands.Parabolic
