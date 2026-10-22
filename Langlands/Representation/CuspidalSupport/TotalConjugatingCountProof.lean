import Langlands.Representation.CuspidalSupport.BlockMap
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement

/-! BZ77 2.8: proof that the total count of minimal conjugating block
permutations is the factorial of the source block count. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF

namespace TotalConjugatingCount

variable {n : ℕ}

section Blocks

/-- Every standard coordinate is a coordinate of some block. -/
theorem index_surjective (B : BlockShape n) (x : Fin n) :
    ∃ (i : Fin B.length) (a : Fin (B.size i)), B.index i a = x := by
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  exact ⟨i, a, rfl⟩

/-- Block `i` has exactly `B.size i` coordinates. -/
theorem card_blockIndex_fiber (B : BlockShape n) (i : Fin B.length) :
    Nat.card {a : Fin n // blockIndex B a = i} = B.size i := by
  have e : {a : Fin n // blockIndex B a = i} ≃ Fin (B.size i) :=
    (B.indexEquiv.symm.subtypeEquiv (p := fun a => blockIndex B a = i)
      (q := fun s : B.Index => s.1 = i) (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype i)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Two block shapes with the same length and the same sizes are equal. -/
theorem shape_ext {C C' : BlockShape n} (hl : C.length = C'.length)
    (hs : ∀ j, C.size j = C'.size (Fin.cast hl j)) : C = C' := by
  obtain ⟨l, s, hp, he⟩ := C
  obtain ⟨l', s', hp', he'⟩ := C'
  dsimp only at hl hs
  subst hl
  have hss : s = s' := funext fun j => hs j
  subst hss
  rfl

end Blocks

section Matrices

variable {R : Type*} [CommRing R]

/-- Membership in the conjugated source Levi, read through the permutation. -/
theorem mem_map_conj_iff (B : BlockShape n) (w : Equiv.Perm (Fin n))
    (h : GeneralLinear n R) :
    h ∈ (B.leviSubgroup R).map (MulAut.conj (permutation n R w)).toMonoidHom ↔
      ∀ a b, blockIndex B a ≠ blockIndex B b → h (w a) (w b) = 0 := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, levi_mem_iff]
  have key : ∀ a b,
      ((permutation n R w)⁻¹ * h * permutation n R w) a b = h (w a) (w b) := by
    intro a b
    rw [mul_permutation_entry, permutation_inv, permutation_mul_entry, inv_inv]
  simp only [key]

/-- A transposition matrix tests whether two coordinates have the same label:
its entries vanish between all coordinates with different labels exactly when
the two transposed coordinates have the same label. -/
theorem swap_entries_vanish_iff [Nontrivial R] {α : Type*} (β : Fin n → α)
    (e : Fin n → Fin n) (he : Function.Injective e) (u v : Fin n) :
    (∀ x y, β x ≠ β y →
        permutation n R (Equiv.swap (e u) (e v)) (e x) (e y) = 0) ↔ β u = β v := by
  constructor
  · intro H
    by_contra huv
    have h := H u v huv
    simp [permutation_entry] at h
  · intro huv x y hxy
    simp only [permutation_entry, ite_eq_right_iff]
    intro hs
    exfalso
    apply hxy
    by_cases hyu : y = u
    · rw [hyu, Equiv.swap_apply_left] at hs
      rw [← he hs, hyu]
      exact huv.symm
    · by_cases hyv : y = v
      · rw [hyv, Equiv.swap_apply_right] at hs
        rw [← he hs, hyv]
        exact huv
      · rw [Equiv.swap_apply_of_ne_of_ne (he.ne hyu) (he.ne hyv)] at hs
        rw [he hs]

end Matrices

section Conjugation

variable {F : Type*} [Field F]

/-- Actual permutation-matrix conjugation carries the source Levi onto the
target Levi exactly when the permutation carries the source block partition
onto the target block partition. -/
theorem conjugatesLevi_iff (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    ConjugatesLevi (F := F) B C w ↔
      ∀ a b, blockIndex B a = blockIndex B b ↔
        blockIndex C (w a) = blockIndex C (w b) := by
  constructor
  · intro hw a b
    have hw' : (B.leviSubgroup F).map (MulAut.conj (permutation n F w)).toMonoidHom =
        C.leviSubgroup F := hw
    have key := SetLike.ext_iff.mp hw' (permutation n F (Equiv.swap (w a) (w b)))
    rw [mem_map_conj_iff, levi_mem_iff] at key
    exact ((swap_entries_vanish_iff (blockIndex B) w w.injective a b).symm.trans key).trans
      (swap_entries_vanish_iff (blockIndex C) id Function.injective_id (w a) (w b))
  · intro H
    show (B.leviSubgroup F).map (MulAut.conj (permutation n F w)).toMonoidHom =
      C.leviSubgroup F
    ext h
    rw [mem_map_conj_iff, levi_mem_iff]
    constructor
    · intro hh x y hxy
      have hne : blockIndex B (w.symm x) ≠ blockIndex B (w.symm y) := by
        intro e
        apply hxy
        simpa using (H _ _).mp e
      simpa using hh (w.symm x) (w.symm y) hne
    · intro hh a b hab
      exact hh (w a) (w b) (fun e => hab ((H a b).mpr e))

variable {B C : BlockShape n} {w : Equiv.Perm (Fin n)}

/-- A conjugating permutation sends source block `i` into target block
`blockMap B C w i`. -/
theorem blockIndex_apply (hw : ConjugatesLevi (F := F) B C w) (a : Fin n) :
    blockIndex C (w a) = blockMap B C w (blockIndex B a) :=
  ((conjugatesLevi_iff B C w).mp hw a
    (B.index (blockIndex B a) ⟨0, B.positive _⟩)).mp (blockIndex_index B _ _).symm

theorem blockMap_injective (hw : ConjugatesLevi (F := F) B C w) :
    Function.Injective (blockMap B C w) := by
  intro i i' h
  have h' := ((conjugatesLevi_iff B C w).mp hw (B.index i ⟨0, B.positive i⟩)
    (B.index i' ⟨0, B.positive i'⟩)).mpr h
  rwa [blockIndex_index, blockIndex_index] at h'

theorem blockMap_surjective (hw : ConjugatesLevi (F := F) B C w) :
    Function.Surjective (blockMap B C w) := by
  intro j
  refine ⟨blockIndex B (w.symm (C.index j ⟨0, C.positive j⟩)), ?_⟩
  rw [← blockIndex_apply hw, Equiv.apply_symm_apply, blockIndex_index]

theorem blockMap_bijective (hw : ConjugatesLevi (F := F) B C w) :
    Function.Bijective (blockMap B C w) :=
  ⟨blockMap_injective hw, blockMap_surjective hw⟩

/-- A conjugating permutation preserves the number of blocks. -/
theorem length_eq (hw : ConjugatesLevi (F := F) B C w) : B.length = C.length := by
  simpa using Fintype.card_of_bijective (blockMap_bijective hw)

/-- Source block `i` and target block `blockMap B C w i` have the same size. -/
theorem size_blockMap (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) :
    C.size (blockMap B C w i) = B.size i := by
  rw [← card_blockIndex_fiber C, ← card_blockIndex_fiber B]
  exact (Nat.card_congr (w.subtypeEquiv (fun a => by
    rw [blockIndex_apply hw, (blockMap_injective hw).eq_iff]))).symm

/-- A conjugating permutation maps source block `i` onto target block
`blockMap B C w i`. -/
theorem range_block (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) :
    Set.range (fun a : Fin (B.size i) => w (B.index i a)) =
      {x | blockIndex C x = blockMap B C w i} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change blockIndex C (w (B.index i a)) = blockMap B C w i
    rw [blockIndex_apply hw, blockIndex_index]
  · intro hx
    obtain ⟨i', a, ha⟩ := index_surjective B (w.symm x)
    have h1 := blockIndex_apply hw (w.symm x)
    rw [Equiv.apply_symm_apply, ← ha, blockIndex_index] at h1
    have hi : i' = i := blockMap_injective hw (h1.symm.trans hx)
    subst hi
    exact ⟨a, show w (B.index _ a) = x by rw [ha, Equiv.apply_symm_apply]⟩

end Conjugation

section Reordering

variable (B : BlockShape n) (σ : Equiv.Perm (Fin B.length))

/-- Reorder the blocks of `B` by `σ`: target block `j` is source block `σ⁻¹ j`. -/
def reorderedShape : BlockShape n where
  length := B.length
  size j := B.size (σ.symm j)
  positive j := B.positive (σ.symm j)
  sum_eq := (Equiv.sum_comp σ.symm B.size).trans B.sum_eq

/-- Send position `a` of source block `i` to position `a` of target block `σ i`. -/
def reorderIndex : B.Index ≃ (reorderedShape B σ).Index where
  toFun x := ⟨σ x.1, Fin.cast (congrArg B.size (σ.symm_apply_apply x.1)).symm x.2⟩
  invFun y := ⟨σ.symm y.1, y.2⟩
  left_inv x := by
    obtain ⟨i, a⟩ := x
    refine Sigma.ext (σ.symm_apply_apply i) ?_
    exact (Fin.heq_ext_iff (congrArg B.size (σ.symm_apply_apply i))).mpr rfl
  right_inv y := by
    obtain ⟨j, b⟩ := y
    refine Sigma.ext (σ.apply_symm_apply j) ?_
    exact (Fin.heq_ext_iff (by simp [reorderedShape])).mpr rfl

/-- The coordinate permutation which moves the blocks of `B` into the order
given by `σ`, keeping the order inside each block. -/
def reorderPerm : Equiv.Perm (Fin n) :=
  (B.indexEquiv.symm.trans (reorderIndex B σ)).trans (reorderedShape B σ).indexEquiv

theorem reorderPerm_index (i : Fin B.length) (a : Fin (B.size i)) :
    reorderPerm B σ (B.index i a) = (reorderedShape B σ).index (σ i)
      (Fin.cast (congrArg B.size (σ.symm_apply_apply i)).symm a) := by
  have h : B.indexEquiv.symm (B.index i a) = ⟨i, a⟩ := B.indexEquiv.symm_apply_apply _
  simp only [reorderPerm, Equiv.trans_apply, h]
  rfl

theorem reorderPerm_symm_index (j : Fin (reorderedShape B σ).length)
    (b : Fin ((reorderedShape B σ).size j)) :
    (reorderPerm B σ).symm ((reorderedShape B σ).index j b) = B.index (σ.symm j) b := by
  have h : (reorderedShape B σ).indexEquiv.symm ((reorderedShape B σ).index j b) = ⟨j, b⟩ :=
    (reorderedShape B σ).indexEquiv.symm_apply_apply _
  simp only [reorderPerm, Equiv.symm_trans_apply, Equiv.symm_symm, h]
  rfl

theorem blockIndex_reorderPerm (x : Fin n) :
    blockIndex (reorderedShape B σ) (reorderPerm B σ x) = σ (blockIndex B x) := by
  obtain ⟨i, a, rfl⟩ := index_surjective B x
  rw [reorderPerm_index, blockIndex_index]
  exact blockIndex_index (reorderedShape B σ) (σ i) _

theorem reorderPerm_minimal :
    IsMinimalRepresentative B (reorderedShape B σ) (reorderPerm B σ) := by
  constructor
  · intro i a b hab
    simp only [reorderPerm_index]
    exact index_strictMono _ _ hab
  · intro j a b hab
    simp only [reorderPerm_symm_index]
    exact index_strictMono B _ hab

theorem reorderPerm_conjugates {F : Type*} [Field F] :
    ConjugatesLevi (F := F) B (reorderedShape B σ) (reorderPerm B σ) :=
  (conjugatesLevi_iff _ _ _).mpr fun a b => by
    rw [blockIndex_reorderPerm, blockIndex_reorderPerm]
    exact σ.injective.eq_iff.symm

end Reordering

section Count

variable {F : Type*} [Field F] (B : BlockShape n)

/-- The element of the total sigma type determined by a block permutation. -/
def reorderElement (σ : Equiv.Perm (Fin B.length)) :
    (C : BlockShape n) × MinimalConjugatingPermutations (F := F) B C :=
  ⟨reorderedShape B σ, ⟨⟨reorderPerm B σ, reorderPerm_minimal B σ⟩,
    reorderPerm_conjugates B σ⟩⟩

/-- The block map of an element of the total sigma type, as natural numbers. -/
def blockValue (x : (C : BlockShape n) × MinimalConjugatingPermutations (F := F) B C)
    (i : Fin B.length) : ℕ :=
  (blockMap B x.1 x.2.val.val i).val

theorem blockValue_reorderElement (σ : Equiv.Perm (Fin B.length)) (i : Fin B.length) :
    blockValue B (reorderElement (F := F) B σ) i = (σ i).val := by
  simp only [blockValue, reorderElement, blockMap, blockIndex_reorderPerm, blockIndex_index]

/-- An element of the total sigma type is determined by its block map:
the target shape by the block sizes, and the permutation by minimality on
each source block. -/
theorem eq_of_blockValue_eq
    (x y : (C : BlockShape n) × MinimalConjugatingPermutations (F := F) B C)
    (h : ∀ i, blockValue B x i = blockValue B y i) : x = y := by
  obtain ⟨C, ⟨w, hmin⟩, hw⟩ := x
  obtain ⟨C', ⟨w', hmin'⟩, hw'⟩ := y
  change ConjugatesLevi (F := F) B C w at hw
  change ConjugatesLevi (F := F) B C' w' at hw'
  change ∀ i, (blockMap B C w i).val = (blockMap B C' w' i).val at h
  have hl : C.length = C'.length := (length_eq hw).symm.trans (length_eq hw')
  have hC : C = C' := by
    apply shape_ext hl
    intro j
    obtain ⟨i, rfl⟩ := blockMap_surjective hw j
    have hj : Fin.cast hl (blockMap B C w i) = blockMap B C' w' i := Fin.ext (h i)
    rw [hj, size_blockMap hw, size_blockMap hw']
  subst hC
  have hπ : blockMap B C w = blockMap B C w' := funext fun i => Fin.ext (h i)
  have hww : w = w' := by
    refine Equiv.ext fun x => ?_
    obtain ⟨i, a, rfl⟩ := index_surjective B x
    have hf := (StrictMono.range_inj_of_wellFoundedLT (hmin.1 i) (hmin'.1 i)).mp
      (by rw [range_block hw, range_block hw', hπ])
    exact congrFun hf a
  subst hww
  rfl

theorem reorderElement_injective :
    Function.Injective (reorderElement (F := F) B) := by
  intro σ τ h
  refine Equiv.ext fun i => Fin.ext ?_
  rw [← blockValue_reorderElement (F := F) B σ i, ← blockValue_reorderElement (F := F) B τ i, h]

theorem reorderElement_surjective :
    Function.Surjective (reorderElement (F := F) B) := by
  intro x
  have hw : ConjugatesLevi (F := F) B x.1 x.2.val.val := x.2.property
  let σ : Equiv.Perm (Fin B.length) :=
    (Equiv.ofBijective _ (blockMap_bijective hw)).trans (finCongr (length_eq hw).symm)
  refine ⟨σ, eq_of_blockValue_eq B _ _ fun i => ?_⟩
  rw [blockValue_reorderElement]
  simp [σ, blockValue]

theorem reorderElement_bijective :
    Function.Bijective (reorderElement (F := F) B) :=
  ⟨reorderElement_injective B, reorderElement_surjective B⟩

/-- The total count over an arbitrary field. -/
theorem finite_and_card_eq :
    Finite ((C : BlockShape n) × MinimalConjugatingPermutations (F := F) B C) ∧
      Nat.card ((C : BlockShape n) × MinimalConjugatingPermutations (F := F) B C) =
        Nat.factorial B.length := by
  refine ⟨Finite.of_surjective _ (reorderElement_surjective (F := F) B), ?_⟩
  rw [← Nat.card_eq_of_bijective _ (reorderElement_bijective (F := F) B), Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end Count

end TotalConjugatingCount

/-- BZ77 2.8, `l(M) = r!`: over every finite p-adic extension and every rank,
the minimal permutations conjugating a standard Levi onto some standard Levi
are counted, over all target shapes, by the factorial of the block count. -/
theorem totalConjugatingCount : TotalConjugatingCountTheorem.{uF} := by
  intro p _ F n B
  exact TotalConjugatingCount.finite_and_card_eq (F := F.Carrier) B

example : TotalConjugatingCountTheorem.{uF} := @totalConjugatingCount.{uF}

end Langlands.CuspidalSupport
