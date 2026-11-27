import Langlands.AllFieldBZ.Representation.CuspidalSupport.ProductConstituentSupportStatement
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductEmbedding
import Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Algebra.MultisetOfFn

/-! Regrouping actual blockwise supercuspidal embeddings adds their supports. -/

noncomputable section

open CategoryTheory

namespace Langlands.AllFieldBZ.CuspidalSupport

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData
open Langlands.Geometric (BlockRefinement)
open Langlands.Classification.SegmentProductCuspidalEmbedding (ofFn_multiset_eq_sum)
open Langlands.AllFieldBZ.Classification (normalizedProduct_embedding_of_factor_embeddings)

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- All constituents of the actual product have the sum of the factor supports. -/
theorem productConstituentSupport : ProductConstituentSupportStatement.{uF, uV} F T := by
  classical
  let := T.topology
  intro n B A s hs I P hP hPI
  have hA (i : Fin B.length) : (A i).IsIrreducible := by
    obtain ⟨_, _, _, _, _, _, hi, _⟩ := hs i
    exact hi
  have he (i : Fin B.length) : ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T),
      T.IsCuspidalSubrepresentation ρ (A i) :=
    glSupercuspidalEmbedding F T (B.size i) (B.positive i) (A i) (hA i)
  choose k ρ hρ using he
  have hsupport (i : Fin B.length) : (List.ofFn (ρ i) : Multiset (CuspidalDatum T)) = s i :=
    glSupercuspidalSupportUniqueness F T (B.size i) (B.positive i) (A i) (hA i) _ _
      ⟨k i, ρ i, rfl, (hρ i).isCuspidalConstituent⟩ (hs i)
  choose hr C hC hAi j hj using hρ
  let S : BlockRefinement B := fun i => T.cuspidalShape (ρ i) (hr i)
  let factors (i : Fin B.length) (j : Fin (S i).length) :
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (S i).size j) := C i j
  let D i := T.cuspidalProductInduced (ρ i) (hr i) (C i)
  obtain ⟨J, hJ⟩ := normalizedProduct_embedding_of_factor_embeddings F T B A D j hj
  let e := B.flattenBlockEquiv S
  let d (q : Fin (B.flatten S).length) : CuspidalDatum.{uV, uF} T :=
    ρ (e.symm q).1 (e.symm q).2
  let reps (q : Fin (B.flatten S).length) :
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (d q).rank) :=
    factors (e.symm q).1 (e.symm q).2
  let flat (q : Fin (B.flatten S).length) :
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((B.flatten S).size q) F.Carrier) :=
    (reps q).obj
  have hd : ∑ q, (d q).rank = n := (B.flatten S).sum_eq
  have hsum : (List.ofFn d : Multiset (CuspidalDatum T)) = ∑ i, s i := by
    rw [ofFn_multiset_eq_sum]
    calc
      ∑ q, ({d q} : Multiset (CuspidalDatum T)) =
          ∑ q : (i : Fin B.length) × Fin (S i).length,
            ({ρ q.1 q.2} : Multiset (CuspidalDatum T)) :=
        Fintype.sum_equiv e.symm _ _ fun _ => rfl
      _ = ∑ i : Fin B.length, ∑ l : Fin (S i).length,
          ({ρ i l} : Multiset (CuspidalDatum T)) :=
        Fintype.sum_sigma' (fun (i : Fin B.length) (l : Fin (S i).length) =>
          ({ρ i l} : Multiset (CuspidalDatum T)))
      _ = ∑ i, s i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (ofFn_multiset_eq_sum (ρ i)).symm.trans (hsupport i)
  have hfactor (q : (i : Fin B.length) × Fin (S i).length) :
      (B.flatten_size_flattenBlockEquiv S q) ▸ flat (e q) = (factors q.1 q.2).obj := by
    have transport (a b : (i : Fin B.length) × Fin (S i).length) (h : a = b) :
        (congrArg (fun q => (S q.1).size q.2) h) ▸ (factors a.1 a.2).obj =
          (factors b.1 b.2).obj := by
      cases h
      rfl
    exact transport _ _ (e.symm_apply_apply q)
  obtain ⟨regroup⟩ := Parabolic.orderedProductRegrouping.{uF, uV} F T n (B.flatten S) B S e
    (fun q => (B.flatten_size_flattenBlockEquiv S q).symm)
    (fun i l x => B.index_index_eq_flatten S ⟨i, l⟩ x) flat
  have regroup' : T.cuspidalProductInduced d hd reps ≅
      (T.normalizedProductInductionFunctor B).obj D := by
    change (T.normalizedProductInductionFunctor (B.flatten S)).obj flat ≅
      (T.normalizedProductInductionFunctor B).obj
        (fun i => (T.normalizedProductInductionFunctor (S i)).obj (fun l => (factors i l).obj))
    simpa only [hfactor] using regroup
  let back := SmoothRep.equivOfIso regroup'.symm
  have hInd : SmoothRep.IsSubrepresentation I (T.cuspidalProductInduced d hd reps) :=
    ⟨SmoothRep.ofHom (back.toIntertwiningMap.comp J), back.injective.comp hJ⟩
  exact ⟨_, d, hsum, hd, reps, fun q => hC (e.symm q).1 (e.symm q).2, hP,
    smoothSubquotientTransitivity ℂ _ _ _ _ hPI hInd.isSubquotient⟩

end Langlands.AllFieldBZ.CuspidalSupport
