import Langlands.Representation.Classification.MinimalIntegralCuspidalBlockWordsProof
import Langlands.Representation.Classification.ConsecutiveIntegralCuspidalWordSegmentHeadProof
import Langlands.Representation.Parabolic.FactorizedInducingSubquotient

/-! Strong segment factors from minimal consecutive cuspidal blocks. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Extract the individual strong segment heads while retaining the actual
whole Jacquet quotient and outer induction embedding. -/
theorem exists_inducingSegmentHeads_of_minimal_consecutiveBlocks :
    letI := T.topology
    ∀ (m : ℕ) (hm : 0 < m) (n : ℕ), 0 < n →
    ∀ (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
      (B : BlockShape n)
      (S : ∀ i : Fin B.length, BlockShape (B.size i))
      (hS : ∀ i, 0 < (S i).length)
      (C : ∀ i : Fin B.length, ∀ j : Fin (S i).length,
        SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (S i).size j))
      (a : Fin B.length → ℤ)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
      (∀ i j,
        (⟨(S i).size j, (C i j).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
            ⟨m, T.supercuspidalClassRealPowerTwist m
              ((a i - (j.val : ℤ) : ℤ) : ℝ) A.isoClass⟩) →
      SmoothRep.IsSubrepresentation π
        ((T.normalizedProductInductionFunctor B).obj (fun i =>
          (T.normalizedProductInductionFunctor (S i)).obj (fun j => (C i j).obj))) →
      (∀ v : List ℤ, IntegralCuspidalJacquetWord F T m n A π v →
        v.Perm (List.ofFn (fun i =>
          List.ofFn (fun j : Fin (S i).length => a i - (j.val : ℤ)))).flatten →
        ¬ List.Lex (· < ·) v (List.ofFn (fun i =>
          List.ofFn (fun j : Fin (S i).length => a i - (j.val : ℤ)))).flatten) →
      ∃ X : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (B.size i) F.Carrier),
        (∀ i, (X i).IsIrreducible) ∧
        (∀ i, (X i).IsAdmissible) ∧
        SmoothRep.IsQuotient (FiniteTensor.externalSmoothObject X)
          ((T.normalizedJacquetFunctor B).obj π) ∧
        SmoothRep.IsSubrepresentation π ((T.normalizedProductInductionFunctor B).obj X) ∧
        ∀ i, ∃ h : (S i).length * m = B.size i,
          T.IsSegmentHead
            (⟨⟨m, hm, T.supercuspidalClassRealPowerTwist m
              ((a i - (((S i).length - 1 : ℕ) : ℤ) : ℤ) : ℝ) A.isoClass⟩,
                (S i).length, hS i⟩ : Segment.{max uF uV, uF} T)
            (h.symm ▸ X i : SmoothRep.{0, uF, max uF uV} ℂ
              (GeneralLinear ((S i).length * m) F.Carrier)) := by
  let := T.topology
  intro m hm n hn A B S hS C a π hπi hπa hπf hlabels hemb hmin
  obtain ⟨X, hXi, hXa, hXY, hXq, hXemb⟩ :=
    Parabolic.exists_factorized_inducing_subquotient F T hn B π
      (fun i => (T.normalizedProductInductionFunctor (S i)).obj (fun j => (C i j).obj))
      hπi hπa hπf hemb
  have hwords := minimalIntegralCuspidalBlockWords F T m n A B S C
    (fun i j => a i - (j.val : ℤ)) X π hlabels hXi hXY hXq.isSubquotient
    (by
      intro i
      apply List.pairwise_ofFn.mpr
      intro j k hjk
      have hjk' : (j.val : ℤ) ≤ (k.val : ℤ) := by
        exact_mod_cast (show j.val ≤ k.val from hjk.le)
      omega)
    hmin
  refine ⟨X, hXi, hXa, hXq, hXemb, ?_⟩
  intro i
  exact consecutiveIntegralCuspidalWordSegmentHead_of_rank F T
    m hm A (S i).length (hS i) (a i) (B.size i) (X i) (hXi i) (hXa i) (hwords i)

end Langlands.Classification
