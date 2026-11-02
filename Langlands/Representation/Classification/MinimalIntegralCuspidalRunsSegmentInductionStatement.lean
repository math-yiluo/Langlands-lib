import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.LanglandsData
import Mathlib.Data.List.Lex

/-! Segment induction extracted from a minimal actual word of consecutive runs. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- A supplied positive consecutive-run decomposition of a least realized word
gives actual strong segment factors, a whole Jacquet quotient, and an embedding. -/
def MinimalIntegralCuspidalRunsSegmentInduction : Prop :=
  letI := T.topology
  ∀ (m : ℕ) (hm : 0 < m) (n : ℕ), 0 < n →
  ∀ (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
    (r : ℕ) (a : Fin r → ℤ) (l : Fin r → ℕ) (hl : ∀ i, 0 < l i)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    IntegralCuspidalJacquetWord F T m n A π
      (List.ofFn (fun i => List.ofFn (fun j : Fin (l i) =>
        a i - (j.val : ℤ)))).flatten →
    (∀ v : List ℤ, IntegralCuspidalJacquetWord F T m n A π v →
      v.Perm (List.ofFn (fun i => List.ofFn (fun j : Fin (l i) =>
        a i - (j.val : ℤ)))).flatten →
      ¬ List.Lex (· < ·) v (List.ofFn (fun i =>
        List.ofFn (fun j : Fin (l i) => a i - (j.val : ℤ)))).flatten) →
    let Δ : Fin r → Segment.{max uF uV, uF} T := fun i =>
      ⟨⟨m, hm, T.supercuspidalClassRealPowerTwist m
        ((a i - ((l i - 1 : ℕ) : ℤ) : ℤ) : ℝ) A.isoClass⟩, l i, hl i⟩
    ∃ hsum : ∑ i, (Δ i).degree = n,
      ∃ X : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (Δ i).degree F.Carrier),
        (∀ i, (X i).IsIrreducible) ∧
        (∀ i, (X i).IsAdmissible) ∧
        (∀ i, T.IsSegmentHead (Δ i) (X i)) ∧
        SmoothRep.IsQuotient (FiniteTensor.externalSmoothObject X)
          ((T.normalizedJacquetFunctor (T.segmentShape Δ hsum)).obj π) ∧
        SmoothRep.IsSubrepresentation π
          ((T.normalizedProductInductionFunctor (T.segmentShape Δ hsum)).obj X)

end Langlands.Classification
