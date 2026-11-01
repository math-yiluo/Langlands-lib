import Langlands.Representation.Parabolic.FlattenedTensorOccurrences
import Langlands.Representation.Parabolic.OrderedRefinementTensorInduction
import Langlands.Group.GL.AdjacentMergeShape

/-! Actual Jacquet tensor occurrences with prescribed ordered fine labels. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.GeneralLinear.BlockShape

open Geometric

variable {n : ℕ} (B C : BlockShape n) (S : BlockRefinement C)
    (e : ((i : Fin C.length) × Fin (S i).length) ≃ Fin B.length)
    (he : ∀ a b : (i : Fin C.length) × Fin (S i).length,
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) → e a < e b)

/-- Reindex canonical flattened labels by the prescribed fine labels. -/
def orderedFlattenLabelEquiv : Fin (C.flatten S).length ≃ Fin B.length :=
  (C.flattenBlockEquiv S).symm.trans e

include e in
/-- Any increasing numbering of the fine blocks has the flattened block count. -/
theorem orderedFlatten_length : (C.flatten S).length = B.length := by
  have h := Fintype.card_congr (orderedFlattenLabelEquiv B C S e)
  simpa only [Fintype.card_fin] using h

include he in
/-- Any increasing numbering is the actual consecutive flattened numbering. -/
theorem orderedFlatten_label (q : (i : Fin C.length) × Fin (S i).length) :
    Fin.cast (orderedFlatten_length B C S e) (C.flattenBlockEquiv S q) = e q := by
  let H : Fin (C.flatten S).length → Fin (C.flatten S).length :=
    fun k => Fin.cast (orderedFlatten_length B C S e).symm
      (e ((C.flattenBlockEquiv S).symm k))
  have hmono : StrictMono H := by
    intro k k' hkk'
    exact he _ _ ((C.flattenBlockEquiv_lt_iff S _ _).mp
      (by simpa only [Equiv.apply_symm_apply] using hkk'))
  have hfix : H (C.flattenBlockEquiv S q) = C.flattenBlockEquiv S q :=
    le_antisymm hmono.apply_le hmono.le_apply
  have hv := congrArg Fin.val hfix
  apply Fin.ext
  simpa only [H, Fin.val_cast, Equiv.symm_apply_apply] using hv.symm

include he in
/-- Ordered fine labels and their ranks determine the standard flattened shape. -/
theorem flatten_eq_of_orderedLabels
    (hs : ∀ q, (S q.1).size q.2 = B.size (e q)) : C.flatten S = B := by
  apply ext_of_size (orderedFlatten_length B C S e)
  intro k
  obtain ⟨q, rfl⟩ := (C.flattenBlockEquiv S).surjective k
  rw [C.flatten_size_flattenBlockEquiv S q, orderedFlatten_label B C S e he q]
  exact hs q

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
    (S : BlockRefinement C)
    (e : ((i : Fin C.length) × Fin (S i).length) ≃ Fin B.length)
    (hs : ∀ q, (S q.1).size q.2 = B.size (e q))
    (he : ∀ a b : (i : Fin C.length) × Fin (S i).length,
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) → e a < e b)

include he in
/-- Extract actual coarse factors with the prescribed ordered inner tensors. -/
theorem exists_factorized_coarseJacquet_of_ordered (hn : 0 < n) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (A : ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size k) F.Carrier)),
      π.IsAdmissible → π.HasFiniteLength →
      (∀ k, (A k).IsIrreducible) → (∀ k, (A k).IsAdmissible) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject A)
        ((T.normalizedJacquetFunctor B).obj π) →
      ∃ X : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier),
        (∀ i, (X i).IsIrreducible) ∧
        (∀ i, (X i).IsAdmissible) ∧
        (∀ i, (X i).HasFiniteLength) ∧
        SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
          ((T.normalizedJacquetFunctor C).obj π) ∧
        (∀ i, SmoothRep.IsSubquotient
          (orderedRefinementTensorFactors F T B C S e hs A i)
          ((T.normalizedJacquetFunctor (S i)).obj (X i))) := by
  let := T.topology
  have hB : C.flatten S = B := B.flatten_eq_of_orderedLabels C S e he hs
  subst B
  have heq : e = C.flattenBlockEquiv S := by
    ext q
    have h := congrArg Fin.val ((C.flatten S).orderedFlatten_label C S e he q)
    simpa only [Fin.val_cast] using h.symm
  subst e
  exact exists_factorized_coarseJacquet_of_flattened T C S hn

include he in
/-- Ordered actual block occurrences return to the specified fine Jacquet module. -/
theorem subquotient_orderedJacquet_of_coarse_factors :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (X : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier))
      (A : ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size k) F.Carrier)),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
        ((T.normalizedJacquetFunctor C).obj π) →
      (∀ i, SmoothRep.IsSubquotient
        (orderedRefinementTensorFactors F T B C S e hs A i)
        ((T.normalizedJacquetFunctor (S i)).obj (X i))) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject A)
        ((T.normalizedJacquetFunctor B).obj π) := by
  let := T.topology
  have hB : C.flatten S = B := B.flatten_eq_of_orderedLabels C S e he hs
  subst B
  have heq : e = C.flattenBlockEquiv S := by
    ext q
    have h := congrArg Fin.val ((C.flatten S).orderedFlatten_label C S e he q)
    simpa only [Fin.val_cast] using h.symm
  subst e
  exact subquotient_flattenedJacquet_of_coarse_factors T C S

end Langlands.Parabolic
