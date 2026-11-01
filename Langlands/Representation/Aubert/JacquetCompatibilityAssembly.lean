import Langlands.Representation.Aubert.JacquetCompatibilityStatement
import Langlands.Representation.Aubert.RankZero
import Langlands.Representation.Geometric.GrothendieckProof
import Langlands.Representation.Geometric.JacquetRegrouping

/-! Actual positive-rank geometric expansion and rank-zero Jacquet compatibility. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic CuspidalSupport SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The intrinsic signed target-refinement sum of actual Jacquet geometric
terms at the outer-block reversal. -/
def jacquetReversalRefinementSum {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier := by
  let := T.topology
  let _ : Fintype (BlockRefinement B) := Fintype.ofFinite _
  exact ∑ Q : BlockRefinement B, (-1 : ℤ) ^ refinementSignExponent B Q •
    canonicalJacquetGeometricTerm.{uF, uV} F T B Q B.reversePermutation

/-- Jacquet restriction after the actual ambient Aubert operator is the
surviving refinement sum. The geometric lemma is applied to each induction
summand before restriction transitivity and fixed-permutation cancellation. -/
theorem jacquetAlternatingOperator_positive {n : ℕ} (hn : 0 < n) (B : BlockShape n) :
    letI := T.topology
    (normalizedJacquetK0.{uF, uV} F T B).comp (alternatingOperator.{uF, uV} F T n) =
      jacquetReversalRefinementSum.{uF, uV} F T B := by
  classical
  let := T.topology
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  let _ : Fintype (BlockRefinement B) := Fintype.ofFinite _
  let _ (C : BlockShape n) : Fintype (MinimalRepresentatives C B) := Fintype.ofFinite _
  choose S R hS hR m e hFormula using
    (fun C : BlockShape n => geometricLemmaGrothendieck.{uF, uV} F T n hn C B)
  have hGeom (C : BlockShape n) :
      (normalizedJacquetK0.{uF, uV} F T B).comp
          (normalizedInductionK0.{uF, uV} F T C) =
        ∑ w : MinimalRepresentatives C B,
          geometricPieceK0.{uF, uV} F T C B w.val (S C w) (R C w)
            (hS C w).2.1 (hR C w).2.1 := by
    apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (C.Levi F.Carrier)
    intro A
    let x := C.finiteLengthClass F.Carrier A.val A.property
    change normalizedJacquetK0 F T B (normalizedInductionK0 F T C x) =
      (∑ w : MinimalRepresentatives C B,
        geometricPieceK0 F T C B w.val (S C w) (R C w)
          (hS C w).2.1 (hR C w).2.1) x
    rw [LinearMap.sum_apply]
    obtain ⟨hP, hEq⟩ := hFormula C A.val A.property
    calc
      _ = ∑ i : Fin (m C), B.finiteLengthClass F.Carrier
          ((CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
            F T C B (e C i).val (S C (e C i)) (R C (e C i))
            (hS C (e C i)).2.1 (hR C (e C i)).2.1).obj A.val) (hP i) := hEq
      _ = ∑ i : Fin (m C),
          geometricPieceK0.{uF, uV} F T C B (e C i).val
            (S C (e C i)) (R C (e C i))
            (hS C (e C i)).2.1 (hR C (e C i)).2.1 x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (geometricPieceK0_finiteLengthClass.{uF, uV} F T C B (e C i).val
          (S C (e C i)) (R C (e C i))
          (hS C (e C i)).2.1 (hR C (e C i)).2.1 A.val A.property (hP i)).symm
      _ = _ := Fintype.sum_equiv (e C) _ _ fun _ => rfl
  calc
    _ = ∑ C : BlockShape n, (-1 : ℤ) ^ (n - C.length) •
        ∑ w : MinimalRepresentatives C B,
          (geometricPieceK0.{uF, uV} F T C B w.val (S C w) (R C w)
            (hS C w).2.1 (hR C w).2.1).comp
              (normalizedJacquetK0.{uF, uV} F T C) := by
      apply LinearMap.ext
      intro x
      change normalizedJacquetK0 F T B (alternatingOperator F T n x) = _
      rw [alternatingOperator_apply, map_sum]
      simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply]
      refine Finset.sum_congr rfl fun C _ => ?_
      congr 1
      have h := LinearMap.congr_fun (hGeom C) (normalizedJacquetK0 F T C x)
      rw [LinearMap.comp_apply, LinearMap.sum_apply] at h
      exact h
    _ = _ := geometricPieces_comp_jacquet_signedSum.{uF, uV} F T B S R
      (fun C w => (hS C w).2.1) (fun C w => (hR C w).2.1)

/-- The exact reversed-Levi Jacquet equality in rank zero, using the actual
rank-zero Aubert maps and the trivial reversal transport. -/
theorem jacquetCompatibility_rankZero (B : BlockShape 0) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (normalizedJacquetK0.{uF, uV} F T B).comp (alternatingOperator.{uF, uV} F T 0) =
      (leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
        (conjugatesLevi_reversePermutation F.Carrier B)).toLinearMap.comp
          ((alternatingOperatorOnLevi.{uF, uV} F T B.reverse).comp
            (normalizedJacquetK0.{uF, uV} F T B.reverse)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [alternatingOperator_rankZero, alternatingOperatorOnLevi_rankZero]
  have hB : B.reverse = B := by
    apply BlockShape.cuts_injective
    ext i
    exact i.elim0
  have hTransport (C : BlockShape 0) (hCB : C = B) (w : Equiv.Perm (Fin 0))
      (hw : ConjugatesLevi (F := F.Carrier) C B w) :
      (leviTransportK0.{uF, uV} F.Carrier C B w hw).toLinearMap.comp
          (normalizedJacquetK0.{uF, uV} F T C) =
        normalizedJacquetK0.{uF, uV} F T B := by
    subst C
    have hmem : w ∈ blockWeyl B := by
      have hw' : w = 1 := Subsingleton.elim _ _
      rw [hw']
      exact Subgroup.one_mem _
    rw [leviTransportK0_eq_id_of_mem_blockWeyl F.Carrier B w hmem]
    simp
  simpa only [LinearMap.comp_id, LinearMap.id_comp] using
    (hTransport B.reverse hB B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B)).symm

end Langlands.Aubert
