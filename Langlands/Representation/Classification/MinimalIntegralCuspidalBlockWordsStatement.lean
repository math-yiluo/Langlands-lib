import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Induction.BlockFactors
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Perm.Basic

/-! Actual decreasing block words forced by global lexicographic minimality. -/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- If actual coarse constituents come from labeled cuspidal products with
decreasing label lists, minimality of their reference concatenation forces
each original block word to occur in its coarse constituent. -/
def MinimalIntegralCuspidalBlockWords : Prop :=
  letI := T.topology
  ∀ (m n : ℕ)
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
    (B : BlockShape n)
    (S : ∀ i : Fin B.length, BlockShape (B.size i))
    (C : ∀ i : Fin B.length, ∀ j : Fin (S i).length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (S i).size j))
    (e : ∀ i : Fin B.length, Fin (S i).length → ℤ)
    (X : ∀ i : Fin B.length,
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    (∀ i j,
      (⟨(S i).size j, (C i j).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
          ⟨m, T.supercuspidalClassRealPowerTwist m (e i j : ℝ) A.isoClass⟩) →
    (∀ i, (X i).IsIrreducible) →
    (∀ i, SmoothRep.IsSubquotient (X i)
      ((T.normalizedProductInductionFunctor (S i)).obj (fun j => (C i j).obj))) →
    SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
      ((T.normalizedJacquetFunctor B).obj π) →
    (∀ i, (List.ofFn (e i)).Pairwise (· ≥ ·)) →
    (∀ v : List ℤ, IntegralCuspidalJacquetWord F T m n A π v →
      v.Perm (List.ofFn (fun i => List.ofFn (e i))).flatten →
      ¬ List.Lex (· < ·) v (List.ofFn (fun i => List.ofFn (e i))).flatten) →
    ∀ i, IntegralCuspidalJacquetWord F T m (B.size i) A (X i) (List.ofFn (e i))

end Langlands.Classification
