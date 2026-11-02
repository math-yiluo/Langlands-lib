import Langlands.Representation.CuspidalSupport.BinaryCuspidalConcatenation
import Langlands.Representation.Induction.EmptyProductUnit

/-! Actual binary concatenation of supplied cuspidal families in all ranks. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.PadicField.TopologicalData.BinaryCuspidalConcatenation

open GeneralLinear CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {T : F.TopologicalData}

theorem length_eq_zero_of_rank_sum_zero {k : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T) (hρ : ∑ i, (ρ i).rank = 0) :
    k = 0 := by
  let : IsEmpty (Fin k) := (T.cuspidalShape ρ hρ).isEmpty_blockIndex_rankZero
  by_contra h
  exact isEmptyElim (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k)

theorem multiset_eq_zero_of_rank_sum_zero {k : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T) (hρ : ∑ i, (ρ i).rank = 0) :
    (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) = 0 := by
  have hk := length_eq_zero_of_rank_sum_zero ρ hρ
  subst k
  simp

private def cuspidalRankEquiv {k m n : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (hm : ∑ i, (ρ i).rank = m) (hn : ∑ i, (ρ i).rank = n)
    (h : n = m)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    (T.cuspidalProductInduced ρ hn A).representation.Equiv
      ((T.cuspidalProductInduced ρ hm A).representation.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).toMonoidHom) := by
  cases h
  letI := T.topology
  rw [GeneralLinear.reindex_finCongr_rfl]
  exact Representation.Equiv.refl _

/-- The left empty cuspidal family acts as the actual unit, with the exact
rank comparison and without retaining an extra carrier lift. -/
def leftZeroProductIso {k l b : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (τ : Fin l → CuspidalDatum.{uV, uF} T)
    (hρ : ∑ i, (ρ i).rank = 0) (hτ : ∑ i, (τ i).rank = b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) :
    letI := T.topology
    T.cuspidalProductInduced τ (hτ.trans (Nat.zero_add b).symm) C ≅
      (T.binaryNormalizedProductFunctor 0 b).obj
        (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C) := by
  letI := T.topology
  let X := T.cuspidalProductInduced ρ hρ A
  let Y := T.cuspidalProductInduced τ hτ C
  let eX : X ≅ T.binaryProductUnit.{uF, max uF uV} :=
    T.emptyProductUnitIso (T.cuspidalShape ρ hρ) (fun i => (A i).obj)
  let eP := (T.binaryNormalizedProductFunctor 0 b).mapIso
    (Iso.prod eX (Iso.refl Y))
  let eU := (T.binaryProductLeftUnitEquiv Y).trans
    (BinaryTensor.liftEquiv _).symm
  let eR := cuspidalRankEquiv τ hτ (hτ.trans (Nat.zero_add b).symm)
    (Nat.zero_add b) C
  exact SmoothRep.mkIso
    (eR.trans (eU.symm.trans (SmoothRep.equivOfIso eP).symm))

/-- The right empty cuspidal family acts as the actual unit. -/
def rightZeroProductIso {k l a : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (τ : Fin l → CuspidalDatum.{uV, uF} T)
    (hρ : ∑ i, (ρ i).rank = a) (hτ : ∑ i, (τ i).rank = 0)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) :
    letI := T.topology
    T.cuspidalProductInduced ρ (hρ.trans (Nat.add_zero a).symm) A ≅
      (T.binaryNormalizedProductFunctor a 0).obj
        (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C) := by
  letI := T.topology
  let X := T.cuspidalProductInduced ρ hρ A
  let Y := T.cuspidalProductInduced τ hτ C
  let eY : Y ≅ T.binaryProductUnit.{uF, max uF uV} :=
    T.emptyProductUnitIso (T.cuspidalShape τ hτ) (fun i => (C i).obj)
  let eP := (T.binaryNormalizedProductFunctor a 0).mapIso
    (Iso.prod (Iso.refl X) eY)
  let eU := (T.binaryProductRightUnitEquiv X).trans
    (BinaryTensor.liftEquiv _).symm
  let eR := cuspidalRankEquiv ρ hρ (hρ.trans (Nat.add_zero a).symm)
    (Nat.add_zero a) A
  exact SmoothRep.mkIso
    (eR.trans (eU.symm.trans (SmoothRep.equivOfIso eP).symm))

/-- Actual cuspidal data and supplied representatives for a binary product.
The compatibility field needs only the original representation witnesses. -/
structure AllRankData {k l a b : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (τ : Fin l → CuspidalDatum.{uV, uF} T)
    (hρ : ∑ i, (ρ i).rank = a) (hτ : ∑ i, (τ i).rank = b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) where
  count : ℕ
  family : Fin count → CuspidalDatum.{uV, uF} T
  rank_sum : ∑ i, (family i).rank = a + b
  representatives : letI := T.topology
    ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (family i).rank)
  represents : (∀ i, (ρ i).IsRepresentedBy (A i)) →
    (∀ i, (τ i).IsRepresentedBy (C i)) →
    ∀ i, (family i).IsRepresentedBy (representatives i)
  count_eq : count = k + l
  multiset_eq : (List.ofFn family : Multiset (CuspidalDatum.{uV, uF} T)) =
    (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) +
      (List.ofFn τ : Multiset (CuspidalDatum.{uV, uF} T))
  productIso : letI := T.topology
    T.cuspidalProductInduced family rank_sum representatives ≅
      (T.binaryNormalizedProductFunctor a b).obj
        (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C)

/-- Concatenate two supplied cuspidal families in every pair of ranks.
Zero ranks retain the other family and its actual representatives. -/
def allRank {k l a b : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (τ : Fin l → CuspidalDatum.{uV, uF} T)
    (hρ : ∑ i, (ρ i).rank = a) (hτ : ∑ i, (τ i).rank = b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) :
    AllRankData ρ τ hρ hτ A C := by
  classical
  by_cases ha : a = 0
  · cases ha
    exact {
      count := l
      family := τ
      rank_sum := hτ.trans (Nat.zero_add b).symm
      representatives := C
      represents := fun _ hC => hC
      count_eq := by rw [length_eq_zero_of_rank_sum_zero ρ hρ, Nat.zero_add]
      multiset_eq := by rw [multiset_eq_zero_of_rank_sum_zero ρ hρ, zero_add]
      productIso := leftZeroProductIso ρ τ hρ hτ A C }
  by_cases hb : b = 0
  · cases hb
    exact {
      count := k
      family := ρ
      rank_sum := hρ.trans (Nat.add_zero a).symm
      representatives := A
      represents := fun hA _ => hA
      count_eq := by rw [length_eq_zero_of_rank_sum_zero τ hτ, Nat.add_zero]
      multiset_eq := by rw [multiset_eq_zero_of_rank_sum_zero τ hτ, add_zero]
      productIso := rightZeroProductIso ρ τ hρ hτ A C }
  let ha' := Nat.pos_of_ne_zero ha
  let hb' := Nat.pos_of_ne_zero hb
  exact {
    count := ((BlockShape.binary a b ha' hb').flatten (refinement ρ τ ha' hb' hρ hτ)).length
    family := flattenedFamily ρ τ ha' hb' hρ hτ
    rank_sum := flattenedFamily_rank_sum ρ τ ha' hb' hρ hτ
    representatives := flattenedRepresentatives ρ τ ha' hb' hρ hτ A C
    represents := flattenedRepresentatives_represents ρ τ ha' hb' hρ hτ A C
    count_eq := flattened_length ρ τ ha' hb' hρ hτ
    multiset_eq := flattenedFamily_multiset ρ τ ha' hb' hρ hτ
    productIso := productIso ρ τ ha' hb' hρ hτ A C }

end Langlands.PadicField.TopologicalData.BinaryCuspidalConcatenation
