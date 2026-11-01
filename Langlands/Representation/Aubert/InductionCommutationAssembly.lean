import Langlands.Representation.Aubert.InductionCommutationStatement
import Langlands.Representation.Geometric.GrothendieckStatement
import Langlands.Representation.Geometric.PieceGrothendieck
import Langlands.Representation.Geometric.RefinementSolomonRegrouping

/-! Actual source-refinement terms and positive-rank commutation assembly. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual induction of the refined induction-after-Jacquet term. -/
def refinementInductionJacquetK0 {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  (normalizedInductionK0.{uF, uV} F T B).comp
    ((normalizedRefinedInductionK0.{uF, uV} F T B S).comp
      (normalizedRefinedJacquetK0.{uF, uV} F T B S))

theorem inductionCommutation_positive_of_piece_comparison
    (hGeo : GeometricLemmaGrothendieckStatement.{uF, uV} F T)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n) :
    letI := T.topology
    (∀ (C : BlockShape n) (w : MinimalRepresentatives B C)
      (S : BlockRefinement B) (R : BlockRefinement C)
      (hS : sourceLevi F.Carrier B C w.val = refinedLevi F.Carrier B S)
      (hR : sourceLevi F.Carrier C B w.val⁻¹ = refinedLevi F.Carrier C R)
      (x : B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier),
      normalizedInductionK0.{uF, uV} F T C
          (geometricPieceK0.{uF, uV} F T B C w.val S R hS hR x) =
        normalizedInductionK0.{uF, uV} F T B
          (normalizedRefinedInductionK0.{uF, uV} F T B S
            (normalizedRefinedJacquetK0.{uF, uV} F T B S x))) →
    (alternatingOperator.{uF, uV} F T n).comp
        (normalizedInductionK0.{uF, uV} F T B) =
      (normalizedInductionK0.{uF, uV} F T B).comp
        (alternatingOperatorOnLevi.{uF, uV} F T B) := by
  classical
  let := T.topology
  intro hPiece
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  let _ : Fintype (BlockRefinement B) := Fintype.ofFinite _
  let _ (C : BlockShape n) : Fintype (MinimalRepresentatives B C) := Fintype.ofFinite _
  choose S R hS hR m e hFormula using hGeo n hn B
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (B.Levi F.Carrier)
  intro A
  let x := B.finiteLengthClass F.Carrier A.val A.property
  have hGeom (C : BlockShape n) :
      normalizedJacquetK0.{uF, uV} F T C
          (normalizedInductionK0.{uF, uV} F T B x) =
        ∑ w : MinimalRepresentatives B C,
          geometricPieceK0.{uF, uV} F T B C w.val (S C w) (R C w)
            (hS C w).2.1 (hR C w).2.1 x := by
    obtain ⟨hP, hEq⟩ := hFormula C A.val A.property
    calc
      _ = ∑ i : Fin (m C), C.finiteLengthClass F.Carrier
          ((CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
            F T B C (e C i).val (S C (e C i)) (R C (e C i))
            (hS C (e C i)).2.1 (hR C (e C i)).2.1).obj A.val) (hP i) := hEq
      _ = ∑ i : Fin (m C),
          geometricPieceK0.{uF, uV} F T B C (e C i).val
            (S C (e C i)) (R C (e C i))
            (hS C (e C i)).2.1 (hR C (e C i)).2.1 x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (geometricPieceK0_finiteLengthClass.{uF, uV} F T B C (e C i).val
          (S C (e C i)) (R C (e C i))
          (hS C (e C i)).2.1 (hR C (e C i)).2.1 A.val A.property (hP i)).symm
      _ = _ := Fintype.sum_equiv (e C) _ _ fun _ => rfl
  let f : BlockRefinement B →
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
    fun Q => refinementInductionJacquetK0.{uF, uV} F T B Q x
  change alternatingOperator.{uF, uV} F T n
      (normalizedInductionK0.{uF, uV} F T B x) =
    normalizedInductionK0.{uF, uV} F T B (alternatingOperatorOnLevi.{uF, uV} F T B x)
  rw [alternatingOperator_apply]
  calc
    _ = refinementSignedSum B S f := by
      unfold refinementSignedSum
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [hGeom C, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      exact hPiece C w (S C w) (R C w) (hS C w).2.1 (hR C w).2.1 x
    _ = ∑ Q : BlockRefinement B, (-1 : ℤ) ^ refinementSignExponent B Q • f Q :=
      refinementSignedSum_eq_refinement_sum F.Carrier B S
        (fun C w => (hS C w).2.1) f
    _ = _ := by
      rw [alternatingOperatorOnLevi_apply, map_sum]
      simp only [map_smul, f, refinementInductionJacquetK0, LinearMap.comp_apply]

end Langlands.Aubert
