import Langlands.Representation.Aubert.JacquetCompatibilityAssembly
import Langlands.Representation.Geometric.OuterReversalGrothendieck

/-! Actual reversed-Levi Jacquet compatibility of the Aubert operator. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem jacquetReversalRefinementSum_eq_of_terms {n : ℕ} (B : BlockShape n)
    (e : BlockRefinement B ≃ BlockRefinement B.reverse)
    (hsign : ∀ Q, refinementSignExponent B.reverse (e Q) = refinementSignExponent B Q) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (∀ Q : BlockRefinement B,
      canonicalJacquetGeometricTerm.{uF, uV} F T B Q B.reversePermutation =
        (leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
          (conjugatesLevi_reversePermutation F.Carrier B)).toLinearMap.comp
            ((normalizedRefinedInductionK0.{uF, uV} F T B.reverse (e Q)).comp
              ((normalizedRefinedJacquetK0.{uF, uV} F T B.reverse (e Q)).comp
                (normalizedJacquetK0.{uF, uV} F T B.reverse)))) →
    jacquetReversalRefinementSum.{uF, uV} F T B =
      (leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
        (conjugatesLevi_reversePermutation F.Carrier B)).toLinearMap.comp
          ((alternatingOperatorOnLevi.{uF, uV} F T B.reverse).comp
            (normalizedJacquetK0.{uF, uV} F T B.reverse)) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hTerm
  let _ : Fintype (BlockRefinement B) := Fintype.ofFinite _
  let _ : Fintype (BlockRefinement B.reverse) := Fintype.ofFinite _
  let tr := leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
    (conjugatesLevi_reversePermutation F.Carrier B)
  apply LinearMap.ext
  intro x
  change (∑ Q : BlockRefinement B, (-1 : ℤ) ^ refinementSignExponent B Q •
      canonicalJacquetGeometricTerm.{uF, uV} F T B Q B.reversePermutation) x =
    tr (alternatingOperatorOnLevi.{uF, uV} F T B.reverse
      (normalizedJacquetK0.{uF, uV} F T B.reverse x))
  rw [alternatingOperatorOnLevi_apply, map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_smul]
  calc
    _ = ∑ Q : BlockRefinement B,
        (-1 : ℤ) ^ refinementSignExponent B.reverse (e Q) •
          tr (normalizedRefinedInductionK0.{uF, uV} F T B.reverse (e Q)
            (normalizedRefinedJacquetK0.{uF, uV} F T B.reverse (e Q)
              (normalizedJacquetK0.{uF, uV} F T B.reverse x))) := by
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [← hsign Q, hTerm Q]
      rfl
    _ = _ := Fintype.sum_equiv e _ _ fun _ => rfl

/-- The surviving signed geometric terms are the actual reversed product-Levi
Aubert operator after reversed Jacquet restriction and inverse transport. -/
theorem jacquetReversalRefinementSum_eq {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    jacquetReversalRefinementSum.{uF, uV} F T B =
      (leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
        (conjugatesLevi_reversePermutation F.Carrier B)).toLinearMap.comp
          ((alternatingOperatorOnLevi.{uF, uV} F T B.reverse).comp
            (normalizedJacquetK0.{uF, uV} F T B.reverse)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply jacquetReversalRefinementSum_eq_of_terms.{uF, uV} F T B
    (outerReverseRefinement B) (refinementSignExponent_outerReverse B)
  intro Q
  let K := B.reverse.flatten (outerReverseRefinement B Q)
  have hK : ConjugatesLevi (F := F.Carrier) K (B.flatten Q) B.reversePermutation :=
    conjugatesLevi_outerReverseFlattened B Q F.Carrier
  rw [canonicalJacquetGeometricTerm_eq.{uF, uV} F T K B Q B.reversePermutation hK]
  exact jacquetGeometricTerm_outerReverse.{uF, uV} F T B Q hK
    (conjugatesLevi_reversePermutation F.Carrier B)

/-- Actual normalized upper Jacquet restriction intertwines the unadjusted
Aubert operators with the specified reversed-to-original Levi transport,
at every natural rank. -/
theorem jacquetCompatibility : JacquetCompatibilityStatement.{uF, uV} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n B
  cases n with
  | zero => exact jacquetCompatibility_rankZero.{uF, uV} F T B
  | succ n =>
      exact (jacquetAlternatingOperator_positive.{uF, uV} F T (Nat.succ_pos n) B).trans
        (jacquetReversalRefinementSum_eq.{uF, uV} F T B)

end Langlands.Aubert
