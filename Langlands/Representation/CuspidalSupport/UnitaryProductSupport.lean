import Langlands.Representation.Classification.BernsteinUnitaryProductIrreducibilityProof
import Langlands.Representation.Classification.SegmentHeadSupportGeneric
import Langlands.Representation.CuspidalSupport.BinaryProductSupport
import Langlands.Representation.Induction.HeadTailBinaryProduct

/-! # Supercuspidal support of a normalized unitary block product -/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem support_rankCast {a b : ℕ} (h : a = b)
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)} (hs : T.IsSupercuspidalSupport A s) :
    T.IsSupercuspidalSupport ((Derivative.generalLinearRankCast T h).obj A) s := by
  cases h
  exact hs

private theorem irreducible_of_rankCast {a b : ℕ} (h : a = b)
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hA : letI := T.topology; ((Derivative.generalLinearRankCast T h).obj A).IsIrreducible) :
    letI := T.topology; A.IsIrreducible := by
  cases h
  exact hA

private theorem rankCast_eq {a b : ℕ} (h : a = b)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    (Derivative.generalLinearRankCast T h).obj A = h ▸ A := by
  cases h
  rfl

private theorem transport_symm_cancel {α : Sort*} (P : α → Sort*)
    {a b : α} (h : a = b) (x : P a) : h.symm ▸ (h ▸ x) = x := by
  cases h
  rfl

set_option maxHeartbeats 500000 in
private theorem singleton_product_support {n : ℕ} (B : BlockShape n) (h : B.length = 1)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → Multiset (CuspidalDatum.{uV, uF} T))
    (hs : ∀ i, T.IsSupercuspidalSupport (σ i) (s i)) :
    T.IsSupercuspidalSupport ((T.normalizedProductInductionFunctor B).obj σ) (∑ i, s i) := by
  let := T.topology
  let i := B.singleBlockIndex h
  have hsize := B.singleBlock_size h i
  let A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) := hsize ▸ σ i
  let τ := fun j => ((B.singleBlock_size h j).symm ▸ A :
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
  have hτ : τ = σ := by
    funext j
    have hj : j = i := B.eq_singleBlockIndex h j
    subst j
    exact transport_symm_cancel
      (fun r => SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
      hsize (σ i)
  have hA : T.IsSupercuspidalSupport A (s i) :=
    (support_rankCast T hsize (hs i)).of_iso (eqToIso (rankCast_eq T hsize (σ i)))
  let e := (T.normalizedProductInductionFunctor B).mapIso (eqToIso hτ.symm) ≪≫
    SmoothRep.mkIso (Parabolic.equivTrans (T.normalizedProductInductionObjEquiv B τ)
      (T.singleBlockTransportedProductEquiv B h A))
  have hsum : ∑ j, s j = s i := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      exact False.elim (hj (B.eq_singleBlockIndex h j))
    · simp
  rw [hsum]
  exact hA.of_iso e.symm

/-- The whole normalized product of irreducible unitarizable factors has
the sum of their supplied supercuspidal supports. -/
def NormalizedUnitaryProductSupportStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, (σ i).representation.IsIrreducible ∧ IsUnitarizable (σ i).representation) →
    ∀ (s : Fin B.length → Multiset (CuspidalDatum.{uV, uF} T)),
      (∀ i, T.IsSupercuspidalSupport (σ i) (s i)) →
      T.IsSupercuspidalSupport ((T.normalizedProductInductionFunctor B).obj σ) (∑ i, s i)

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 700000 in
private theorem normalizedUnitaryProductSupport_aux (l : ℕ) :
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n), B.length = l →
      ∀ (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, (σ i).representation.IsIrreducible ∧ IsUnitarizable (σ i).representation) →
      ∀ (s : Fin B.length → Multiset (CuspidalDatum.{uV, uF} T)),
        (∀ i, T.IsSupercuspidalSupport (σ i) (s i)) →
        T.IsSupercuspidalSupport ((T.normalizedProductInductionFunctor B).obj σ) (∑ i, s i) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    let := T.topology
    intro n hn B hl σ hσ s hs
    rcases l with _ | _ | k
    · have : IsEmpty (Fin B.length) := ⟨fun i => by have := i.isLt; omega⟩
      have hn0 : n = 0 := by simpa using B.sum_eq.symm
      omega
    · exact singleton_product_support T B hl σ s hs
    · let tail := (T.normalizedProductInductionFunctor (B.tailShape hl)).obj
        (fun j => σ (B.tailIndex hl j))
      have htail : T.IsSupercuspidalSupport tail (∑ j, s (B.tailIndex hl j)) :=
        ih (k + 1) (by omega) _ (B.tailRank_pos hl) (B.tailShape hl) rfl
          (fun j => σ (B.tailIndex hl j)) (fun j => hσ (B.tailIndex hl j))
          (fun j => s (B.tailIndex hl j)) (fun j => hs (B.tailIndex hl j))
      let product := (T.normalizedProductInductionFunctor B).obj σ
      let binary := (T.binaryNormalizedProductFunctor (B.headRank hl) (B.tailRank hl)).obj
        (σ (B.headIndex hl), tail)
      let e := T.headTailBinaryProductIso B hl σ
      have hproduct : product.IsIrreducible :=
        (Classification.bernsteinUnitaryProductIrreducibility.{uF,uV} F T n B σ hσ).1
      have hbinary : binary.IsIrreducible := irreducible_of_rankCast T
        (B.headRank_add_tailRank hl) ((isIrreducible_iff_of_equiv (SmoothRep.equivOfIso e)).mp hproduct)
      have hsBinary := T.binaryProductConstituentSupport (hs (B.headIndex hl)) htail hbinary
        (Classification.SegmentHeadSupport.isSubquotient_refl binary)
      have hsum : ∑ j, s j = s (B.headIndex hl) + ∑ j, s (B.tailIndex hl j) := by
        calc
          _ = ∑ j : Fin (k + 2), s (Fin.cast hl.symm j) :=
            (Equiv.sum_comp (finCongr hl.symm) s).symm
          _ = _ := Fin.sum_univ_succ _
      rw [hsum]
      exact (support_rankCast T (B.headRank_add_tailRank hl) hsBinary).of_iso e.symm

/-- The finite support sum for the irreducible unitary product. -/
theorem normalizedUnitaryProduct_hasSupercuspidalSupport :
    NormalizedUnitaryProductSupportStatement.{uF, uV} T := by
  intro n hn B
  exact normalizedUnitaryProductSupport_aux T B.length n hn B rfl

end Langlands.PadicField.TopologicalData
