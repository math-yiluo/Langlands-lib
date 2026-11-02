import Langlands.Representation.Derivative.BinaryDerivativeSupportAggregation
import Langlands.Representation.Induction.HeadTailBinaryProduct
import Langlands.Representation.Derivative.ProductDerivativesFiniteLength

/-! Actual factor witnesses and support sums for derivatives of ordered products. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory

namespace Langlands.Derivative.ProductDerivativeSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- One actual simple constituent of a factor derivative, with a supplied support
and a prescribed property of its derivative order and support. -/
structure FactorSupportData {a : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (P : ℕ → Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop) where
  order : ℕ
  order_le : order ≤ a
  factor : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a - order) F.Carrier)
  irreducible : letI := T.topology; factor.IsIrreducible
  occurs : letI := T.topology
    SmoothRep.IsSubquotient factor ((generalLinearDerivative T ψ a order order_le).obj A)
  cuspidalSupport : Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T)
  support : T.IsSupercuspidalSupport factor cuspidalSupport
  allowed : P order cuspidalSupport

/-- A selected actual constituent for each original factor. Its derivative orders
sum to the original order, and its supports sum to a support of `D`. -/
structure SupportData {n d : ℕ} (B : GeneralLinear.BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - d) F.Carrier))
    (P : Fin B.length → ℕ →
      Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop) where
  factors : ∀ i, FactorSupportData T ψ (σ i) (P i)
  order_sum : ∑ i, (factors i).order = d
  support : T.IsSupercuspidalSupport D (∑ i, (factors i).cuspidalSupport)

private theorem rankCast_irreducible {a b : ℕ} (h : a = b)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible) :
    letI := T.topology; ((generalLinearRankCast T h).obj D).IsIrreducible := by
  cases h
  exact hD

private theorem rankCast_support_back {a b : ℕ} (h : a = b)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (s : Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T))
    (hs : T.IsSupercuspidalSupport ((generalLinearRankCast T h.symm).obj D) s) :
    T.IsSupercuspidalSupport D s := by
  cases h
  exact hs

private theorem derivative_rankCast_occurrence {a b d : ℕ} (h : a = b)
    (hd : d ≤ b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (b - d) F.Carrier))
    (hDA : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ b d hd).obj
        ((generalLinearRankCast T h).obj A))) :
    letI := T.topology
    SmoothRep.IsSubquotient
      ((generalLinearRankCast T (congrArg (fun r => r - d) h).symm).obj D)
      ((generalLinearDerivative T ψ a d (by omega)).obj A) := by
  cases h
  exact hDA

private theorem rankCast_binary_support {a b r : ℕ} (h : a + b = r)
    {E : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {H : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    {D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
    {s t : Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T)}
    (hE : T.IsSupercuspidalSupport E s) (hH : T.IsSupercuspidalSupport H t)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (E, H)))) :
    T.IsSupercuspidalSupport D (s + t) := by
  cases h
  exact T.binaryProductConstituentSupport hE hH hD hDP

private theorem transport_symm_cancel {α : Sort*} (P : α → Sort*)
    {a b : α} (h : a = b) (x : P a) : h.symm ▸ (h ▸ x) = x := by
  subst b
  rfl

private theorem rankCast_obj_transport {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T h).obj A = h ▸ A := by
  cases h
  rfl

private theorem singleFamily_eq {n : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = 1)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun j => ((B.singleBlock_size h j).symm ▸
      ((B.singleBlock_size h (B.singleBlockIndex h)) ▸ σ (B.singleBlockIndex h)) :
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))) = σ := by
  let := T.topology
  funext j
  have hj := B.eq_singleBlockIndex h j
  subst j
  exact transport_symm_cancel
    (fun r => SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) _ _

private def singletonProductIso {n : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = 1)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj σ ≅
      (generalLinearRankCast T (B.singleBlock_size h (B.singleBlockIndex h))).obj
        (σ (B.singleBlockIndex h)) := by
  let := T.topology
  let i := B.singleBlockIndex h
  let A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
    (B.singleBlock_size h i) ▸ σ i
  let τ := fun j => ((B.singleBlock_size h j).symm ▸ A :
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
  let e := Parabolic.equivTrans (T.normalizedProductInductionObjEquiv B τ)
    (T.singleBlockTransportedProductEquiv B h A)
  let eF := (T.normalizedProductInductionFunctor B).mapIso
    (eqToIso (singleFamily_eq T B h σ).symm)
  exact eF ≪≫ SmoothRep.mkIso e ≪≫
    eqToIso (rankCast_obj_transport T (B.singleBlock_size h i) (σ i)).symm

private theorem sum_singleBlock {M : Type*} [AddCommMonoid M] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (h : B.length = 1) (f : Fin B.length → M) :
    ∑ j, f j = f (B.singleBlockIndex h) := by
  apply Finset.sum_eq_single (B.singleBlockIndex h)
  · intro j _ hj
    exact False.elim (hj (B.eq_singleBlockIndex h j))
  · simp

private def singletonSupportData {n d : ℕ} (hd : d ≤ n)
    (B : GeneralLinear.BlockShape n) (h : B.length = 1)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - d) F.Carrier))
    (P : Fin B.length → ℕ →
      Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop)
    (hSupport : letI := T.topology
      ∀ i k (hk : k ≤ B.size i)
        (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i - k) F.Carrier)),
        E.IsIrreducible →
        SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)) →
        ∃ s, P i k s ∧ T.IsSupercuspidalSupport E s)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n d hd).obj
        ((T.normalizedProductInductionFunctor B).obj σ))) :
    SupportData T ψ B σ D P := by
  let := T.topology
  let i := B.singleBlockIndex h
  let e := B.singleBlock_size h i
  let D₀ := (generalLinearRankCast T (congrArg (fun r => r - d) e).symm).obj D
  have hd₀ : d ≤ B.size i := by omega
  have hD₀ : D₀.IsIrreducible := rankCast_irreducible T _ D hD
  have hocc := derivative_rankCast_occurrence T ψ e hd (σ i) D
    (hDP.of_iso_right ((generalLinearDerivative T ψ n d hd).mapIso
      (singletonProductIso T B h σ)))
  have hs := hSupport i d hd₀ D₀ hD₀ hocc
  let s := Classical.choose hs
  let f : FactorSupportData T ψ (σ i) (P i) :=
    { order := d
      order_le := hd₀
      factor := D₀
      irreducible := hD₀
      occurs := hocc
      cuspidalSupport := s
      support := (Classical.choose_spec hs).2
      allowed := (Classical.choose_spec hs).1 }
  let fs : ∀ j, FactorSupportData T ψ (σ j) (P j) := fun j => by
    have hj := B.eq_singleBlockIndex h j
    subst j
    exact f
  have hsum : ∑ j, (fs j).cuspidalSupport = s := sum_singleBlock B h _
  exact
    { factors := fs
      order_sum := sum_singleBlock B h _
      support := by
        rw [hsum]
        exact rankCast_support_back T (congrArg (fun r => r - d) e) D s
          (Classical.choose_spec hs).2 }

private def headTailPi {n k : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = k + 2) (X : Fin B.length → Sort*)
    (head : X (B.headIndex h)) (tail : ∀ j, X (B.tailIndex h j)) :
    ∀ i, X i := by
  rcases B with ⟨l, size, hp, hs⟩
  dsimp at h
  subst l
  exact Fin.cases head tail

private theorem headTailPi_head {n k : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = k + 2) (X : Fin B.length → Sort*)
    (head : X (B.headIndex h)) (tail : ∀ j, X (B.tailIndex h j)) :
    headTailPi B h X head tail (B.headIndex h) = head := by
  rcases B with ⟨l, size, hp, hs⟩
  dsimp at h
  subst l
  rfl

private theorem headTailPi_tail {n k : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = k + 2) (X : Fin B.length → Sort*)
    (head : X (B.headIndex h)) (tail : ∀ j, X (B.tailIndex h j))
    (j : Fin (k + 1)) :
    headTailPi B h X head tail (B.tailIndex h j) = tail j := by
  rcases B with ⟨l, size, hp, hs⟩
  dsimp at h
  subst l
  rfl

private theorem sum_headTail {M : Type*} [AddCommMonoid M] {n k : ℕ}
    (B : GeneralLinear.BlockShape n) (h : B.length = k + 2) (f : Fin B.length → M) :
    ∑ i, f i = f (B.headIndex h) + ∑ j, f (B.tailIndex h j) := by
  calc
    _ = ∑ i : Fin (k + 2), f (Fin.cast h.symm i) :=
      (Equiv.sum_comp (finCongr h.symm) f).symm
    _ = _ := Fin.sum_univ_succ _

private theorem supportData_nonempty (l : ℕ) :
    ∀ {n d : ℕ}, 0 < n → ∀ (hd : d ≤ n) (B : GeneralLinear.BlockShape n),
    B.length = l →
    ∀ (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - d) F.Carrier))
    (P : Fin B.length → ℕ →
      Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop),
    (letI := T.topology;
      ∀ i k (hk : k ≤ B.size i),
        ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)).HasFiniteLength) →
    (letI := T.topology;
      ∀ i k (hk : k ≤ B.size i)
        (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i - k) F.Carrier)),
        E.IsIrreducible →
        SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)) →
        ∃ s, P i k s ∧ T.IsSupercuspidalSupport E s) →
    (letI := T.topology; D.IsIrreducible) →
    (letI := T.topology;
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n d hd).obj
        ((T.normalizedProductInductionFunctor B).obj σ))) →
    Nonempty (SupportData T ψ B σ D P) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro n d hn hd B hB σ D P hFinite hSupport hD hDP
    let := T.topology
    rcases l with _ | l
    · have hempty : IsEmpty (Fin B.length) :=
        ⟨fun i => by have := i.isLt; omega⟩
      have hn0 : n = 0 := by simpa using B.sum_eq.symm
      omega
    rcases l with _ | m
    · exact ⟨singletonSupportData T ψ hd B hB σ D P hSupport hD hDP⟩
    · have h : B.length = m + 2 := hB
      let A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.headRank h) F.Carrier) :=
        σ (B.headIndex h)
      let C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.tailRank h) F.Carrier) :=
        (T.normalizedProductInductionFunctor (B.tailShape h)).obj
          (fun j => σ (B.tailIndex h j))
      let e := B.headRank_add_tailRank h
      let D₀ := (generalLinearRankCast T (congrArg (fun r => r - d) e).symm).obj D
      have hd₀ : d ≤ B.headRank h + B.tailRank h := by omega
      have hD₀ : D₀.IsIrreducible := rankCast_irreducible T _ D hD
      have hocc := derivative_rankCast_occurrence T ψ e hd
        ((T.binaryNormalizedProductFunctor (B.headRank h) (B.tailRank h)).obj (A, C)) D
        (hDP.of_iso_right ((generalLinearDerivative T ψ n d hd).mapIso
          (T.headTailBinaryProductIso B h σ)))
      have hTailFinite := ProductDerivativesFiniteLength.product_derivatives T ψ (m + 1)
        (B.tailRank_pos h) (B.tailShape h) rfl (fun j => σ (B.tailIndex h j))
        (fun j => hFinite (B.tailIndex h j))
      let f := BinaryDerivativeSupport.factorData T ψ hd₀ A C
        (hFinite (B.headIndex h)) hTailFinite D₀ hD₀ hocc
      have hs := hSupport (B.headIndex h) f.index.val.1
        (leibnizIndices_left_le f.index.property) f.left f.left_irreducible f.left_occurs
      let s := Classical.choose hs
      let head : FactorSupportData T ψ A (P (B.headIndex h)) :=
        { order := f.index.val.1
          order_le := leibnizIndices_left_le f.index.property
          factor := f.left
          irreducible := f.left_irreducible
          occurs := f.left_occurs
          cuspidalSupport := s
          support := (Classical.choose_spec hs).2
          allowed := (Classical.choose_spec hs).1 }
      obtain ⟨tail⟩ := ih (m + 1) (by omega) (B.tailRank_pos h)
        (leibnizIndices_right_le f.index.property) (B.tailShape h) rfl
        (fun j => σ (B.tailIndex h j)) f.right (fun j => P (B.tailIndex h j))
        (fun j => hFinite (B.tailIndex h j)) (fun j => hSupport (B.tailIndex h j))
        f.right_irreducible f.right_occurs
      let fs := headTailPi B h (fun i => FactorSupportData T ψ (σ i) (P i))
        head tail.factors
      have hsum : ∑ i, (fs i).cuspidalSupport =
          head.cuspidalSupport + ∑ j, (tail.factors j).cuspidalSupport := by
        rw [sum_headTail B h]
        simp only [fs, headTailPi_head, headTailPi_tail]
        rfl
      have hsumSupport := rankCast_binary_support T (leibnizIndices_rank f.index.property)
        head.support tail.support hD₀ ⟨f.subspace, f.kernel, ⟨f.occurrenceIso⟩⟩
      refine ⟨{ factors := fs, order_sum := ?_, support := ?_ }⟩
      · rw [sum_headTail B h]
        simp only [fs, headTailPi_head, headTailPi_tail]
        exact (congrArg (fun r => head.order + r) tail.order_sum).trans
          (leibnizIndices_sum f.index.property)
      · rw [hsum]
        exact rankCast_support_back T (congrArg (fun r => r - d) e) D _ hsumSupport

/-- Choose actual simple derivative constituents for all original factors, whose
orders add to the supplied order and whose supplied support multisets add to a
support of the supplied simple constituent of the ordered-product derivative. -/
def supportData {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (B : GeneralLinear.BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - d) F.Carrier))
    (P : Fin B.length → ℕ →
      Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop)
    (hFinite : letI := T.topology
      ∀ i k (hk : k ≤ B.size i),
        ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)).HasFiniteLength)
    (hSupport : letI := T.topology
      ∀ i k (hk : k ≤ B.size i)
        (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i - k) F.Carrier)),
        E.IsIrreducible →
        SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)) →
        ∃ s, P i k s ∧ T.IsSupercuspidalSupport E s)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n d hd).obj
        ((T.normalizedProductInductionFunctor B).obj σ))) :
    SupportData T ψ B σ D P :=
  Classical.choice (supportData_nonempty T ψ B.length hn hd B rfl σ D P
    hFinite hSupport hD hDP)

/-- The same construction after taking a supplied subquotient of the original
ordered product before differentiation. -/
def supportDataOfSubquotient {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (B : GeneralLinear.BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hQ : letI := T.topology
      SmoothRep.IsSubquotient Q ((T.normalizedProductInductionFunctor B).obj σ))
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - d) F.Carrier))
    (P : Fin B.length → ℕ →
      Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) → Prop)
    (hFinite : letI := T.topology
      ∀ i k (hk : k ≤ B.size i),
        ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)).HasFiniteLength)
    (hSupport : letI := T.topology
      ∀ i k (hk : k ≤ B.size i)
        (E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i - k) F.Carrier)),
        E.IsIrreducible →
        SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)) →
        ∃ s, P i k s ∧ T.IsSupercuspidalSupport E s)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDQ : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n d hd).obj Q)) :
    SupportData T ψ B σ D P := by
  let := T.topology
  have hQ' := ExactSmoothTransport.map_isSubquotient _
    (generalLinearDerivativeExactness.{uF, max uF uV} F T ψ n d hd) hQ
  exact supportData T ψ hn hd B σ D P hFinite hSupport hD
    (smoothSubquotientTransitivity ℂ _ _ _ _ hDQ hQ')

end Langlands.Derivative.ProductDerivativeSupport
