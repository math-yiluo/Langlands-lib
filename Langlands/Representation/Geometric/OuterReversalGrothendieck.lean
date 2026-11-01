import Langlands.Representation.Geometric.OuterReversalInduction
import Langlands.Representation.Geometric.JacquetPieceGrothendieck

/-! Actual outer reversal on refined induction and surviving geometric terms on K0. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport SmoothRep Parabolic

universe uF uV

section Coordinates

variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- Outer relabelling on the full exact finite-length smooth K0 of the actual
refined subgroup, with the contravariant direction required by induction. -/
def outerReverseRefinedLeviK0 :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F B.reverse (outerReverseRefinement B S)) ≃ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ (refinedLevi F B S) :=
  FiniteLengthGrothendieckGroup.pullbackEquiv
    (outerReverseRefinedLeviEquivContinuous B F S)

/-- Continuous inverse flattened conjugation is the actual outer relabelling. -/
theorem leviConjugationContinuous_outerReverseFlattened_symm
    (h : ConjugatesLevi (F := F) (B.reverse.flatten (outerReverseRefinement B S))
      (B.flatten S) B.reversePermutation) :
    (leviConjugationContinuous B.reversePermutation h).symm =
      outerReverseFlattenedLeviEquivContinuous B S F := by
  apply ContinuousMulEquiv.ext
  intro m
  exact leviConjugation_outerReverseFlattened_symm B S F h m

/-- Unflattening both sides of the flattened outer reversal gives the literal
refined subgroup relabelling. -/
theorem outerReverseFlattenedLeviEquivContinuous_unflatten :
    (flattenedLeviEquivContinuous F B S).symm.trans
        ((outerReverseFlattenedLeviEquivContinuous B S F).trans
          (flattenedLeviEquivContinuous F B.reverse (outerReverseRefinement B S))) =
      outerReverseRefinedLeviEquivContinuous B F S := by
  apply ContinuousMulEquiv.ext
  intro m
  change flattenedLeviEquiv F B.reverse (outerReverseRefinement B S)
      ((flattenedLeviEquiv F B.reverse (outerReverseRefinement B S)).symm
        (outerReverseRefinedLeviEquiv B F S
          (flattenedLeviEquiv F B S ((flattenedLeviEquiv F B S).symm m)))) = _
  simp only [MulEquiv.apply_symm_apply]
  rfl

end Coordinates

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Actual normalized refined induction commutes with outer reindexing on the
full exact finite-length smooth K0. -/
theorem normalizedRefinedInductionK0_outerReverse :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    (normalizedRefinedInductionK0.{uF, uV} F T B S).comp
        (FiniteLengthGrothendieckGroup.pullback
          (outerReverseRefinedLeviEquivContinuous B F.Carrier S)) =
      (FiniteLengthGrothendieckGroup.pullback
        (outerReverseLeviEquivContinuous B F.Carrier)).comp
          (normalizedRefinedInductionK0.{uF, uV} F T B.reverse
            (outerReverseRefinement B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply FiniteLengthGrothendieckGroup.hom_ext_object
    ℂ (refinedLevi F.Carrier B.reverse (outerReverseRefinement B S))
  intro A
  let P := SmoothRep.pullback (outerReverseRefinedLeviEquivContinuous B F.Carrier S) A.val
  let I := (T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj P
  let I' := (T.normalizedRefinedInductionFunctor.{uF, max uF uV}
    B.reverse (outerReverseRefinement B S)).obj A.val
  let Q := SmoothRep.pullback (outerReverseLeviEquivContinuous B F.Carrier) I'
  have hP : P.HasFiniteLength := pullbackFunctor_preservesFiniteLength _ _ A.property
  have hI : I.HasFiniteLength :=
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).1 n B S P hP
  have hI' : I'.HasFiniteLength :=
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).1 n B.reverse
      (outerReverseRefinement B S) A.val A.property
  have hQ : Q.HasFiniteLength := pullbackFunctor_preservesFiniteLength _ I' hI'
  change normalizedRefinedInductionK0 F T B S
      (FiniteLengthGrothendieckGroup.pullback _
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) =
    FiniteLengthGrothendieckGroup.pullback _
      (normalizedRefinedInductionK0 F T B.reverse (outerReverseRefinement B S)
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property))
  rw [FiniteLengthGrothendieckGroup.pullback_ofRepresentation _ _ _ hP,
    normalizedRefinedInductionK0_finiteLengthClass F T B S P hP hI,
    normalizedRefinedInductionK0_finiteLengthClass F T B.reverse
      (outerReverseRefinement B S) A.val A.property hI']
  change FiniteLengthGrothendieckGroup.ofRepresentation I hI =
    FiniteLengthGrothendieckGroup.pullback _
      (FiniteLengthGrothendieckGroup.ofRepresentation I' hI')
  rw [FiniteLengthGrothendieckGroup.pullback_ofRepresentation _ I' hI' hQ]
  apply FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
  exact (T.normalizedRefinedInduced_outerReverseEquiv B S A.val.representation).symm

/-- The same actual induction comparison uses exactly the inverse-conjugation
transport in the Jacquet compatibility target. -/
theorem normalizedRefinedInductionK0_outerReverse_transport
    (h : ConjugatesLevi (F := F.Carrier) B.reverse B B.reversePermutation) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    (normalizedRefinedInductionK0.{uF, uV} F T B S).comp
        (FiniteLengthGrothendieckGroup.pullback
          (outerReverseRefinedLeviEquivContinuous B F.Carrier S)) =
      (leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation h).toLinearMap.comp
        (normalizedRefinedInductionK0.{uF, uV} F T B.reverse
          (outerReverseRefinement B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change _ = (FiniteLengthGrothendieckGroup.pullback
    (leviConjugationContinuous B.reversePermutation h).symm).comp _
  rw [leviConjugationContinuous_outerReverse_symm B F.Carrier h]
  exact normalizedRefinedInductionK0_outerReverse.{uF, uV} F T B S

/-- The actual flattened inverse-conjugation transport, between the two
flattened coordinate equivalences, is refined outer reversal on exact K0. -/
theorem flattenedLeviK0_outerReverse_transport
    (h : ConjugatesLevi (F := F.Carrier)
      (B.reverse.flatten (outerReverseRefinement B S)) (B.flatten S) B.reversePermutation) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    (flattenedLeviK0.{uF, uV} F.Carrier B S).symm.toLinearMap.comp
        ((leviTransportK0.{uF, uV} F.Carrier
          (B.reverse.flatten (outerReverseRefinement B S)) (B.flatten S)
          B.reversePermutation h).toLinearMap.comp
            (flattenedLeviK0.{uF, uV} F.Carrier B.reverse
              (outerReverseRefinement B S)).toLinearMap) =
      FiniteLengthGrothendieckGroup.pullback
        (outerReverseRefinedLeviEquivContinuous B F.Carrier S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change (FiniteLengthGrothendieckGroup.pullback
    (flattenedLeviEquivContinuous F.Carrier B S).symm).comp
      ((FiniteLengthGrothendieckGroup.pullback
        (leviConjugationContinuous B.reversePermutation h).symm).comp
          (FiniteLengthGrothendieckGroup.pullback
            (flattenedLeviEquivContinuous F.Carrier B.reverse
              (outerReverseRefinement B S)))) = _
  rw [leviConjugationContinuous_outerReverseFlattened_symm B S F.Carrier h,
    ← FiniteLengthGrothendieckGroup.pullback_trans,
    ← FiniteLengthGrothendieckGroup.pullback_trans,
    outerReverseFlattenedLeviEquivContinuous_unflatten]

/-- The surviving reversal geometric term is exactly reversed refined
induction after refined and coarse Jacquet restriction, transported to the
original Levi by actual inverse conjugation. -/
theorem jacquetGeometricTerm_outerReverse
    (h : ConjugatesLevi (F := F.Carrier)
      (B.reverse.flatten (outerReverseRefinement B S)) (B.flatten S) B.reversePermutation)
    (hB : ConjugatesLevi (F := F.Carrier) B.reverse B B.reversePermutation) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    jacquetGeometricTerm.{uF, uV} F T
        (B.reverse.flatten (outerReverseRefinement B S)) B S B.reversePermutation h =
      (leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation hB).toLinearMap.comp
        ((normalizedRefinedInductionK0.{uF, uV} F T B.reverse
          (outerReverseRefinement B S)).comp
            ((normalizedRefinedJacquetK0.{uF, uV} F T B.reverse
              (outerReverseRefinement B S)).comp
                (normalizedJacquetK0.{uF, uV} F T B.reverse))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hMiddle := flattenedLeviK0_outerReverse_transport.{uF, uV} F T B S h
  have hInd := normalizedRefinedInductionK0_outerReverse_transport.{uF, uV} F T B S hB
  have hJac := normalizedFlattenedJacquetK0_eq.{uF, uV}
    F T B.reverse (outerReverseRefinement B S)
  apply LinearMap.ext
  intro x
  have hJ : normalizedJacquetK0 F T (B.reverse.flatten (outerReverseRefinement B S)) x =
      flattenedLeviK0 F.Carrier B.reverse (outerReverseRefinement B S)
        (normalizedRefinedJacquetK0 F T B.reverse (outerReverseRefinement B S)
          (normalizedJacquetK0 F T B.reverse x)) :=
    (LinearMap.congr_fun hJac x).symm
  change normalizedRefinedInductionK0 F T B S
      ((flattenedLeviK0 F.Carrier B S).symm
        (leviTransportK0 F.Carrier _ _ B.reversePermutation h
          (normalizedJacquetK0 F T (B.reverse.flatten (outerReverseRefinement B S)) x))) =
    leviTransportK0 F.Carrier B.reverse B B.reversePermutation hB
      (normalizedRefinedInductionK0 F T B.reverse (outerReverseRefinement B S)
        (normalizedRefinedJacquetK0 F T B.reverse (outerReverseRefinement B S)
          (normalizedJacquetK0 F T B.reverse x)))
  rw [hJ]
  exact (congrArg (normalizedRefinedInductionK0 F T B S)
    (LinearMap.congr_fun hMiddle _)).trans (LinearMap.congr_fun hInd _)

end Langlands.Geometric
