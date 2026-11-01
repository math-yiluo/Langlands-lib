import Langlands.Representation.Aubert.InvolutivityStatement
import Langlands.Representation.Aubert.InductionCommutationProof
import Langlands.Representation.Aubert.RefinementCancellation
import Langlands.Representation.Aubert.WholeShape
import Langlands.Representation.Parabolic.FlattenedJacquetGrothendieck

/-! The actual unadjusted Aubert operator squares to the identity in every rank. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem nestedInductionJacquet_apply {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) :
    letI := T.topology
    ∀ x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier,
      normalizedInductionK0.{uF, uV} F T B
        (normalizedRefinedInductionK0.{uF, uV} F T B S
          (normalizedRefinedJacquetK0.{uF, uV} F T B S
            (normalizedJacquetK0.{uF, uV} F T B x))) =
      normalizedInductionK0.{uF, uV} F T (B.flatten S)
        (normalizedJacquetK0.{uF, uV} F T (B.flatten S) x) := by
  let := T.topology
  intro x
  exact LinearMap.congr_fun
    (normalizedComposedInductionK0_comp_composedJacquetK0.{uF, uV} F T B S) x

/-- The unadjusted Aubert endomorphism is an involution on every virtual class
of the actual exact finite-length smooth Grothendieck group in every rank. -/
theorem involutivity : InvolutivityStatement.{uF, uV} F T := by
  let := T.topology
  classical
  intro n
  let : Fintype (BlockShape n) := Fintype.ofFinite _
  let (B : BlockShape n) : Fintype (BlockRefinement B) := Fintype.ofFinite _
  apply LinearMap.ext
  intro x
  change alternatingOperator.{uF, uV} F T n
    (alternatingOperator.{uF, uV} F T n x) = x
  have hc (B : BlockShape n)
      (y : B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier) :
      alternatingOperator.{uF, uV} F T n (normalizedInductionK0 F T B y) =
        normalizedInductionK0 F T B (alternatingOperatorOnLevi F T B y) :=
    LinearMap.congr_fun (inductionCommutation.{uF, uV} F T n B) y
  let f : BlockShape n → GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF}
      n F.Carrier := fun C => normalizedInductionK0 F T C (normalizedJacquetK0 F T C x)
  calc
    _ = ∑ B : BlockShape n, ((-1 : ℤ) ^ (n - B.length)) •
        alternatingOperator.{uF, uV} F T n
          (normalizedInductionK0 F T B (normalizedJacquetK0 F T B x)) := by
      rw [alternatingOperator_apply F T n x, map_sum]
      simp only [map_smul]
    _ = ∑ B : BlockShape n, ((-1 : ℤ) ^ (n - B.length)) •
        normalizedInductionK0 F T B
          (alternatingOperatorOnLevi F T B (normalizedJacquetK0 F T B x)) := by
      simp_rw [hc]
    _ = refinementAlternatingSum f := by
      change _ = ∑ B : BlockShape n, ∑ S : BlockRefinement B,
        ((-1 : ℤ) ^ (n - B.length) * (-1 : ℤ) ^ (n - (B.flatten S).length)) •
          f (B.flatten S)
      apply Finset.sum_congr rfl
      intro B _
      rw [alternatingOperatorOnLevi_apply, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [map_smul, smul_smul, refinementSignExponent_eq,
        nestedInductionJacquet_apply F T B S]
      rfl
    _ = f ((BlockShape.cutEquiv n).symm ∅) := refinementAlternatingSum_eq f
    _ = x := by
      have hwhole :
          (normalizedInductionK0.{uF, uV} F T ((BlockShape.cutEquiv n).symm ∅)).comp
              (normalizedJacquetK0.{uF, uV} F T ((BlockShape.cutEquiv n).symm ∅)) =
            LinearMap.id := by
        cases n with
        | zero => exact inductionJacquetK0_rankZero.{uF, uV} F T _
        | succ n =>
            exact inductionJacquetK0_of_cuts_eq_empty.{uF, uV} F T _
              (Nat.succ_pos n) (BlockShape.cuts_cutEquiv_symm _)
      exact LinearMap.congr_fun hwhole x

end Langlands.Aubert
