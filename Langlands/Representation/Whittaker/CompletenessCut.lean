import Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement
import Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Category.Twist
import Langlands.Representation.Twist.SmoothProof

/-!
# Whittaker completeness: cutting a block product into two

A normalized product `τ_1 × ⋯ × τ_k` of block representations is cut after its first
`c` blocks, with `0 < c < k`. Twisting the blocks after the cut by `|det|^u` (`u`
real) gives the product `τ_u`. The module proves that `τ_u` is equivalent to the
deformed two-block representation `ρ_u` of JPSS 1983, Section (4.5): the canonical
normalized lower induction of the tail product twisted by `|det|^u` and the head
product. The equivalence regroups the blocks (`orderedProductRegrouping`), moves the
common determinant twist of the tail out of its product
(`normalizedProductDeterminantTwistEquiv`), and turns the upper product of the head
and the tail into the lower induction of the tail and the head
(`glOppositeProductReversal`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Whittaker.CompletenessCut

open GeneralLinear RankinSelberg Geometric PadicField

universe uF uW uX

/-- The coordinate of a block coordinate: the sizes of the earlier blocks plus the
coordinate inside the block. -/
theorem blockShape_index_val {n : ℕ} (B : BlockShape n) (i : Fin B.length)
    (x : Fin (B.size i)) :
    (B.index i x).val = (∑ j : Fin i.val, B.size (Fin.castLE i.isLt.le j)) + x.val := by
  simp only [BlockShape.index, Function.Embedding.coeFn_mk, BlockShape.indexEquiv,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]

section Sizes

variable {k : ℕ} (m : Fin k → ℕ)

/-- The block sizes `m i + 1`, extended by `0` beyond the last block. -/
def extSize (q : ℕ) : ℕ := if hq : q < k then m ⟨q, hq⟩ + 1 else 0

theorem extSize_val (i : Fin k) : extSize m i.val = m i + 1 := by
  simp [extSize, i.isLt]

/-- A sum of consecutive block sizes is a range sum of the extended sizes. -/
theorem sum_shift (a n : ℕ) (g : Fin n → ℕ) (f : Fin n → Fin k)
    (hg : ∀ q, g q = m (f q) + 1) (hf : ∀ q, (f q).val = a + q.val) :
    ∑ q, g q = ∑ q ∈ Finset.range n, extSize m (a + q) := by
  rw [← Fin.sum_univ_eq_sum_range (fun q => extSize m (a + q))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hg, ← hf q, extSize_val]

theorem succBlockShape_index_val {t : ℕ} (h : ∑ i, (m i + 1) = t + 1) (i : Fin k)
    (x : Fin (m i + 1)) :
    ((succBlockShape m h).index i x).val = ∑ q ∈ Finset.range i, extSize m q + x := by
  rw [blockShape_index_val]
  congr 1
  simpa using sum_shift m 0 i.val _ (Fin.castLE i.isLt.le) (fun _ => rfl)
    (fun q => (zero_add _).symm)

end Sizes

section Regroup

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
variable (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
variable (hsz : ∀ a, (S a.1).size a.2 = B.size (e a))
variable (hc : ∀ j k (x : Fin ((S j).size k)),
  D.index j ((S j).index k x) = B.index (e ⟨j, k⟩) (Fin.cast (hsz ⟨j, k⟩) x))

include hc in
/-- Ordered regrouping of a normalized block product, stated for actual normalized
products. The inner products of the refinement are given by blocks `σ' j l` equal to
the transported original blocks. -/
def regroupEquiv
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier))
    (σ' : letI := T.topology
      ∀ j l, SmoothRep.{0, uF, uW} ℂ (GeneralLinear ((S j).size l) F.Carrier))
    (hσ : letI := T.topology; ∀ j l,
      ((hsz ⟨j, l⟩).symm ▸ σ (e ⟨j, l⟩) :
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear ((S j).size l) F.Carrier)) = σ' j l)
    {W : Fin D.length → Type uX} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (τ : ∀ j, Representation ℂ (GeneralLinear (D.size j) F.Carrier) (W j))
    (δ : letI := T.topology; ∀ j,
      (T.normalizedProductInduced (S j) (fun l => (σ' j l).representation)).Equiv (τ j)) :
    letI := T.topology
    (T.normalizedProductInduced B (fun i => (σ i).representation)).Equiv
      (T.normalizedProductInduced D τ) := by
  letI := T.topology
  refine (equivOfRepresentationEq (T.normalizedProductInductionFunctor_obj B σ)).symm.trans
    (T.normalizedProductRegroupingToEquiv (Parabolic.orderedProductRegrouping F T)
      B D S e hsz hc σ τ (fun j => ?_))
  refine (T.normalizedProductInductionFamilyEqEquiv (S j) (σ' := σ' j) ?_).trans
    ((T.normalizedProductInductionObjEquiv (S j) (σ' j)).trans (δ j))
  funext l
  exact hσ j l

end Regroup

/-- A cut of `k` blocks into a nonempty head `0, …, c - 1` and a nonempty tail
`c, …, k - 1`. -/
structure Cut (k : ℕ) where
  /-- The number of head blocks. -/
  c : ℕ
  pos : 0 < c
  lt : c < k

namespace Cut

variable {k : ℕ} (C : Cut k)

/-- The number of blocks of part `i`. In the order of `twoBlockDeformedInduced`, part
`0` is the tail and part `1` the head. -/
def length (i : Fin 2) : ℕ := if i = 0 then k - C.c else C.c

/-- The first block of part `i`. -/
def start (i : Fin 2) : ℕ := if i = 0 then C.c else 0

@[simp] theorem length_zero : C.length 0 = k - C.c := rfl
@[simp] theorem length_one : C.length 1 = C.c := rfl
@[simp] theorem start_zero : C.start 0 = C.c := rfl
@[simp] theorem start_one : C.start 1 = 0 := rfl

theorem start_add_length (i : Fin 2) : C.start i + C.length i ≤ k := by
  have := C.lt
  unfold start length
  split_ifs <;> omega

theorem length_pos (i : Fin 2) : 0 < C.length i := by
  have := C.pos
  have := C.lt
  unfold length
  split_ifs <;> omega

/-- The `l`-th block of part `i`. -/
def index (i : Fin 2) (l : Fin (C.length i)) : Fin k :=
  ⟨C.start i + l, by have := C.start_add_length i; omega⟩

theorem index_val (i : Fin 2) (l : Fin (C.length i)) :
    (C.index i l).val = C.start i + l := rfl

/-- A block of part `i` lies after the cut exactly when `i = 0`. -/
theorem le_index_iff (i : Fin 2) (l : Fin (C.length i)) :
    C.c ≤ (C.index i l).val ↔ i = 0 := by
  have hl := l.isLt
  rw [index_val]
  unfold start length at *
  by_cases hi : i = 0
  · simp only [hi, ite_true] at hl ⊢
    simp
  · simp only [hi, ite_false] at hl ⊢
    simp only [iff_false]
    omega

variable (m : Fin k → ℕ)

/-- The rank of part `i`. -/
def rank (i : Fin 2) : ℕ := ∑ l : Fin (C.length i), (m (C.index i l) + 1)

/-- One less than the rank of part `i`. -/
def size (i : Fin 2) : ℕ := C.rank m i - 1

theorem sum_eq_size_add_one (i : Fin 2) :
    ∑ l : Fin (C.length i), (m (C.index i l) + 1) = C.size m i + 1 := by
  have hpos : 0 < C.rank m i :=
    Finset.sum_pos (fun _ _ => Nat.succ_pos _) ⟨⟨0, C.length_pos i⟩, Finset.mem_univ _⟩
  unfold size
  unfold rank at hpos ⊢
  omega

theorem rank_eq (i : Fin 2) :
    C.rank m i = ∑ q ∈ Finset.range (C.length i), extSize m (C.start i + q) :=
  sum_shift m _ _ _ (C.index i) (fun _ => rfl) (fun _ => rfl)

theorem sum_size {t : ℕ} (h : ∑ i, (m i + 1) = t + 1) :
    ∑ i : Fin 2, (C.size m i + 1) = t + 1 := by
  have hk : ∑ i, (m i + 1) = ∑ q ∈ Finset.range k, extSize m (0 + q) :=
    sum_shift m 0 k _ id (fun _ => rfl) (fun q => (zero_add _).symm)
  have hsplit : ∑ q ∈ Finset.range k, extSize m q =
      ∑ q ∈ Finset.range (C.c + (k - C.c)), extSize m q := by
    rw [Nat.add_sub_cancel' C.lt.le]
  rw [Fin.sum_univ_two, ← C.sum_eq_size_add_one, ← C.sum_eq_size_add_one, ← h, hk]
  change C.rank m 0 + C.rank m 1 = _
  rw [C.rank_eq, C.rank_eq]
  simp only [start_zero, start_one, length_zero, length_one, zero_add]
  rw [hsplit, Finset.sum_range_add, add_comm]

/-- The block shape of part `i`. -/
abbrev partShape (i : Fin 2) : BlockShape (C.size m i + 1) :=
  succBlockShape (fun l => m (C.index i l)) (C.sum_eq_size_add_one m i)

theorem partShape_index_val (i : Fin 2) (l : Fin (C.length i))
    (x : Fin (m (C.index i l) + 1)) :
    ((C.partShape m i).index l x).val =
      ∑ q ∈ Finset.range l, extSize m (C.start i + q) + x := by
  rw [blockShape_index_val]
  congr 1
  exact sum_shift m _ _ _ (fun q => C.index i (Fin.castLE l.isLt.le q)) (fun _ => rfl)
    (fun _ => rfl)

/-- The shape of the two parts, tail first. -/
abbrev twoShape {t : ℕ} (h : ∑ i, (m i + 1) = t + 1) : BlockShape (t + 1) :=
  succBlockShape (C.size m) (C.sum_size m h)

/-- The blocks of the two parts enumerate all blocks, head first. -/
def labelEquiv : (Σ j : Fin 2, Fin (C.length j.rev)) ≃ Fin k :=
  Equiv.ofBijective (fun a => C.index a.1.rev a.2) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · rintro ⟨j, l⟩ ⟨j', l'⟩ hEq
      change C.index j.rev l = C.index j'.rev l' at hEq
      have hv : C.start j.rev + l = C.start j'.rev + l' := congrArg Fin.val hEq
      have h1 := C.le_index_iff j.rev l
      have h2 := C.le_index_iff j'.rev l'
      rw [hEq] at h1
      have hrev : j.rev = j'.rev := by
        have key : ∀ a b : Fin 2, (a = 0 ↔ b = 0) → a = b := by decide
        exact key _ _ (h1.symm.trans h2)
      have hjj : j = j' := Fin.rev_injective hrev
      subst hjj
      have hll : l = l' := Fin.ext (by omega)
      rw [hll]
    · simp only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_two]
      change C.length 1 + C.length 0 = k
      have := C.lt
      simp only [length_one, length_zero]
      omega

theorem labelEquiv_apply (a : Σ j : Fin 2, Fin (C.length j.rev)) :
    C.labelEquiv a = C.index a.1.rev a.2 := rfl

theorem regroup_index {t : ℕ} (h : ∑ i, (m i + 1) = t + 1) (j : Fin 2)
    (l : Fin (C.length j.rev)) (x : Fin (m (C.index j.rev l) + 1)) :
    (C.twoShape m h).reverse.index j ((C.partShape m j.rev).index l x) =
      (succBlockShape m h).index (C.labelEquiv ⟨j, l⟩) x := by
  apply Fin.ext
  have hv : ((C.labelEquiv ⟨j, l⟩ : Fin k) : ℕ) = C.start j.rev + l := rfl
  rw [blockShape_index_val, partShape_index_val, succBlockShape_index_val, hv]
  rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
  · have h0 : ∑ j' : Fin (0 : Fin 2).val,
        (C.twoShape m h).reverse.size (Fin.castLE (Fin.isLt (0 : Fin 2)).le j') = 0 :=
      Fin.sum_univ_zero _
    have hs : C.start (Fin.rev 0) = 0 := rfl
    rw [h0, hs]
    simp
  · have h1 : ∑ j' : Fin (1 : Fin 2).val,
        (C.twoShape m h).reverse.size (Fin.castLE (Fin.isLt (1 : Fin 2)).le j') =
          ∑ q ∈ Finset.range C.c, extSize m q := by
      refine (Fin.sum_univ_one _).trans ?_
      change C.size m 1 + 1 = _
      rw [← C.sum_eq_size_add_one]
      change C.rank m 1 = _
      rw [C.rank_eq]
      simp
    have hs : C.start (Fin.rev 1) = C.c := rfl
    rw [h1, hs, Finset.sum_range_add]
    omega

section Representations

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {V : Fin k → Type uW} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))

/-- The blocks after the cut twisted by `|det|^u`. -/
def cutTwist (u : ℝ) :
    ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i) :=
  fun i => Langlands.twist
    (F.canonicalTopologicalData.determinantPowerCharacter (m i + 1)
      (if C.c ≤ i.val then u else 0))
    (τ i)

theorem cutTwist_zero : C.cutTwist m F τ 0 = τ := by
  funext i
  simp only [cutTwist, ite_self, PadicField.TopologicalData.determinantPowerCharacter,
    realPowerCharacter_zero, twist_one]

/-- The normalized product of the blocks of part `i`. -/
abbrev partProduct (i : Fin 2) :=
  F.canonicalNormalizedProductInduced (C.partShape m i) (fun l => τ (C.index i l))

/-- The `|det|^s` twist of the product of part `i`, with `s = u` on the tail and
`s = 0` on the head, is the product of the twisted blocks of part `i`. -/
def partTwistEquiv (u : ℝ) (i : Fin 2) :
    (twoBlockDeformedBlocks F (C.size m) (C.partProduct m F τ) (u : ℂ) i).Equiv
      (F.canonicalNormalizedProductInduced (C.partShape m i)
        (fun l => C.cutTwist m F τ u (C.index i l))) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  let s : ℝ := if i = 0 then u else 0
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s,
      isOpen_ker_realPowerCharacter _ F.canonicalTopologicalData.isOpen_ker_normalizedAbsUnits s⟩
  have hs : (if i = 0 then (u : ℂ) else 0) = ((s : ℝ) : ℂ) := by
    simp only [s]
    split_ifs <;> simp
  have h1 : twoBlockDeformedBlocks F (C.size m) (C.partProduct m F τ) (u : ℂ) i =
      Langlands.twist (χ.toMonoidHom.comp determinant)
        (F.canonicalNormalizedProductInduced (C.partShape m i) (fun l => τ (C.index i l))) := by
    simp only [twoBlockDeformedBlocks, hs,
      PadicField.TopologicalData.determinantComplexPower_ofReal]
    rfl
  have h2 : (fun l => Langlands.twist (χ.toMonoidHom.comp determinant) (τ (C.index i l))) =
      fun l => C.cutTwist m F τ u (C.index i l) := by
    funext l
    simp only [cutTwist, C.le_index_iff]
    rfl
  (equivOfRepresentationEq h1).trans
    ((F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv _ χ _).trans
      (F.canonicalTopologicalData.normalizedProductInducedEquiv _
        (fun l => equivOfRepresentationEq (congrFun h2 l))))

/-- The blocks after the cut twisted by `|det|^u`, as smooth representations. -/
def smoothCutTwist (hs : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (τ i))
    (u : ℝ) :
    letI := F.canonicalTopologicalData.topology
    ∀ i, SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  fun i => SmoothRep.of (C.cutTwist m F τ u i)
    ((isSmooth_twist_iff _ _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter _ _)).mpr (hs i))

end Representations

end Cut

section Reverse

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The deformed two-block representation is the upper normalized product of its
reversed blocks. -/
theorem twoBlockDeformedInduced_reverse {t : ℕ} (m : Fin 2 → ℕ)
    (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin 2 → Type uX} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (σ i)) (u : ℂ) :
    Nonempty ((twoBlockDeformedInduced F m h σ u).Equiv
      (F.canonicalTopologicalData.normalizedProductInduced (succBlockShape m h).reverse
        (V := fun j => W j.rev) (fun j => twoBlockDeformedBlocks F m σ u j.rev))) := by
  let T := F.canonicalTopologicalData
  let _ := T.topology
  have hs : ∀ i, IsSmooth (twoBlockDeformedBlocks F m σ u i) := fun i =>
    (isSmooth_twist_iff _ _ (T.isOpen_ker_determinantComplexPower _ _)).mpr (hσ i)
  obtain ⟨E, -, -⟩ := glOppositeProductReversal p F T (t + 1) (succBlockShape m h) W
    (twoBlockDeformedBlocks F m σ u) hs
  exact ⟨E⟩

/-- An ordered regrouping of a normalized block product into the reversed two-part
shape, followed by the block reversal: if the inner products of the regrouping are the
reversed deformed blocks, the block product is equivalent to the deformed two-block
representation. -/
theorem nonempty_equiv_twoBlockDeformedInduced {t : ℕ} (m : Fin 2 → ℕ)
    (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin 2 → Type uX} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ₂ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ₂ : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (σ₂ i)) (u : ℂ)
    (B : BlockShape (t + 1)) (S : BlockRefinement (succBlockShape m h).reverse)
    (e : ((j : Fin (succBlockShape m h).reverse.length) × Fin (S j).length) ≃ Fin B.length)
    (hsz : ∀ a, (S a.1).size a.2 = B.size (e a))
    (hc : ∀ j k (x : Fin ((S j).size k)),
      (succBlockShape m h).reverse.index j ((S j).index k x) =
        B.index (e ⟨j, k⟩) (Fin.cast (hsz ⟨j, k⟩) x))
    (σ : letI := F.canonicalTopologicalData.topology
      ∀ i, SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear (B.size i) F.Carrier))
    (σ' : letI := F.canonicalTopologicalData.topology
      ∀ j l, SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear ((S j).size l) F.Carrier))
    (hσ : letI := F.canonicalTopologicalData.topology; ∀ j l,
      ((hsz ⟨j, l⟩).symm ▸ σ (e ⟨j, l⟩) :
        SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear ((S j).size l) F.Carrier)) = σ' j l)
    (δ : letI := F.canonicalTopologicalData.topology; ∀ j,
      (F.canonicalTopologicalData.normalizedProductInduced (S j)
        (fun l => (σ' j l).representation)).Equiv (twoBlockDeformedBlocks F m σ₂ u j.rev)) :
    letI := F.canonicalTopologicalData.topology
    Nonempty ((F.canonicalTopologicalData.normalizedProductInduced B
        (fun i => (σ i).representation)).Equiv (twoBlockDeformedInduced F m h σ₂ u)) :=
  (twoBlockDeformedInduced_reverse F m h σ₂ hσ₂ u).map fun E =>
    (regroupEquiv F.canonicalTopologicalData B _ S e hsz hc σ σ' hσ _ δ).trans E.symm

end Reverse

namespace Cut

variable {k : ℕ} (C : Cut k) (m : Fin k → ℕ)

section Representations

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {V : Fin k → Type uW} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))

/-- The cut product `τ_u` is equivalent to the deformed two-block representation `ρ_u`
of the tail and head products. -/
theorem cutEquiv {t : ℕ} (h : ∑ i, (m i + 1) = t + 1)
    (hs : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (τ i)) (u : ℝ) :
    Nonempty ((F.canonicalNormalizedProductInduced (succBlockShape m h)
        (C.cutTwist m F τ u)).Equiv
      (twoBlockDeformedInduced F (C.size m) (C.sum_size m h) (C.partProduct m F τ)
        (u : ℂ))) := by
  have hp : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (C.partProduct m F τ i) :=
    fun i => F.canonicalTopologicalData.isSmooth_normalizedProductInduced (C.partShape m i)
      (fun l => τ (C.index i l))
  exact nonempty_equiv_twoBlockDeformedInduced F (C.size m) (C.sum_size m h)
    (C.partProduct m F τ) hp (u : ℂ) (succBlockShape m h) (fun j => C.partShape m j.rev)
    C.labelEquiv (fun _ => rfl) (C.regroup_index m h) (C.smoothCutTwist m F τ hs u)
    (fun j l => C.smoothCutTwist m F τ hs u (C.index j.rev l)) (fun _ _ => rfl)
    (fun j => (C.partTwistEquiv m F τ u j.rev).symm)

end Representations

end Cut

end Langlands.Whittaker.CompletenessCut
