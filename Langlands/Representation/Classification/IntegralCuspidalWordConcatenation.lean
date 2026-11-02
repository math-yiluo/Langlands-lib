import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.SegmentProductConcatenation
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences

/-! Reassemble actual integral words of coarse Jacquet factors. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open GeneralLinear Geometric Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData)

theorem integralCuspidalJacquetWord_concatenate :
    letI := T.topology
    ∀ (m n : ℕ)
      (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
      (B : BlockShape n)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (X : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (B.size i) F.Carrier))
      (w : Fin B.length → List ℤ),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
        ((T.normalizedJacquetFunctor B).obj π) →
      (∀ i, IntegralCuspidalJacquetWord F T m (B.size i) A (X i) (w i)) →
      IntegralCuspidalJacquetWord F T m n A π (List.ofFn w).flatten := by
  let := T.topology
  intro m n A B π X w hX hw
  classical
  choose S C e he hlabels hocc using hw
  let D : ∀ k : Fin (B.flatten S).length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier)
        (n := (B.flatten S).size k) :=
    fun k => C ((B.flattenBlockEquiv S).symm k).1
      ((B.flattenBlockEquiv S).symm k).2
  let f : Fin (B.flatten S).length → ℤ :=
    fun k => e ((B.flattenBlockEquiv S).symm k).1
      ((B.flattenBlockEquiv S).symm k).2
  have hcast {r s : ℕ} (h : r = s)
      (Y : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
      HEq (h ▸ Y : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear s F.Carrier)) Y := by
    cases h
    rfl
  have hdep (a b : Σ i, Fin (S i).length) (h : a = b) :
      HEq (C a.1 a.2).obj (C b.1 b.2).obj := by
    cases h
    rfl
  have hblocks (i : Fin B.length) :
      flattenedBlockTensor T B S (fun k => (D k).obj) i =
        FiniteTensor.externalSmoothObject (fun j => (C i j).obj) := by
    apply congrArg FiniteTensor.externalSmoothObject
    funext j
    have hc : HEq ((D (B.flattenBlockEquiv S ⟨i, j⟩)).obj) (C i j).obj :=
      hdep _ _ ((B.flattenBlockEquiv S).symm_apply_apply ⟨i, j⟩)
    exact eq_of_heq ((hcast
      (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩)
      ((D (B.flattenBlockEquiv S ⟨i, j⟩)).obj)).trans hc)
  have hwords : List.ofFn f = (List.ofFn w).flatten := by
    rw [show w = fun i => List.ofFn (e i) from funext he]
    exact FiniteConcatenation.ofFn_finSigmaFinEquiv (fun i => (S i).length) e
  refine ⟨B.flatten S, D, f, hwords.symm, ?_, ?_⟩
  · intro k
    exact hlabels ((B.flattenBlockEquiv S).symm k).1
      ((B.flattenBlockEquiv S).symm k).2
  · apply subquotient_flattenedJacquet_of_coarse_factors T B S π X
      (fun k => (D k).obj) hX
    intro i
    rw [hblocks i]
    exact hocc i

end Langlands.Classification
