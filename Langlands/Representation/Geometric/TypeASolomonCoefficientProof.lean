import Langlands.Representation.Geometric.TypeASolomonCoefficientStatement
import Langlands.Representation.Geometric.BlockWeylCutProof
import Langlands.Representation.Geometric.BlockShapeCutCounts
import Langlands.Representation.Geometric.PermutationDescents

/-! A finite cut-toggling proof of the signed type-A Solomon coefficient identity. -/

namespace Langlands.Geometric

open GeneralLinear

variable {n : ℕ}

namespace TypeASolomon

/-- The left coordinate of an interior edge. -/
def edgeLo (e : Fin (n - 1)) : Fin n := ⟨e.val, by omega⟩

/-- The right coordinate of an interior edge. -/
def edgeHi (e : Fin (n - 1)) : Fin n := ⟨e.val + 1, by omega⟩

@[simp] theorem val_lo (e : Fin (n - 1)) : (edgeLo e).val = e.val := rfl

@[simp] theorem val_hi (e : Fin (n - 1)) : (edgeHi e).val = e.val + 1 := rfl

theorem lo_lt_hi (e : Fin (n - 1)) : edgeLo e < edgeHi e := by
  rw [Fin.lt_def, val_lo, val_hi]
  omega

theorem lo_injective : Function.Injective (edgeLo (n := n)) := by
  intro e f h
  exact Fin.ext (by simpa using congrArg Fin.val h)

/-- The two coordinates of an edge lie in one block exactly when the edge is not a cut. -/
theorem blockIndex_lo_eq_hi_iff (B : BlockShape n) (e : Fin (n - 1)) :
    blockIndex B (edgeLo e) = blockIndex B (edgeHi e) ↔ e ∉ B.cuts := by
  rw [blockIndex_eq_iff_cut_sides]
  constructor
  · intro h he
    have hs := h e he
    simp only [val_lo, val_hi] at hs
    omega
  · intro h j hj
    have hne : e.val ≠ j.val := by
      intro hej
      have he : e = j := Fin.ext hej
      exact h (he ▸ hj)
    simp only [val_lo, val_hi]
    omega

theorem mem_descents_iff (w : Equiv.Perm (Fin n)) (e : Fin (n - 1)) :
    e ∈ permutationDescents w ↔ w (edgeHi e) < w (edgeLo e) :=
  mem_permutationDescents w e

/-- The source order condition of a minimal representative. -/
def SourceIncreasing (B : BlockShape n) (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ j, StrictMono (fun a : Fin (B.size j) => w (B.index j a))

/-- A permutation increasing on the blocks of `B` increases along any pair of one block. -/
theorem lt_of_sameBlock (B : BlockShape n) {w : Equiv.Perm (Fin n)}
    (hw : SourceIncreasing B w) {x y : Fin n} (hxy : x < y)
    (hs : blockIndex B x = blockIndex B y) : w x < w y := by
  obtain ⟨a, ha⟩ := exists_index_of_blockIndex_eq B (a := x) rfl
  obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq B (a := y) hs.symm
  have hab : a < b := by
    rw [← (index_strictMono B (blockIndex B x)).lt_iff_lt, ha, hb]
    exact hxy
  have h := hw (blockIndex B x) hab
  dsimp only at h
  rwa [ha, hb] at h

theorem le_of_sameBlock (B : BlockShape n) {w : Equiv.Perm (Fin n)}
    (hw : SourceIncreasing B w) {x y : Fin n} (hxy : x ≤ y)
    (hs : blockIndex B x = blockIndex B y) : w x ≤ w y := by
  rcases hxy.lt_or_eq with h | h
  · exact (lt_of_sameBlock B hw h hs).le
  · rw [h]

/-- Blocks are intervals. -/
theorem blockIndex_eq_of_between (B : BlockShape n) {a x b : Fin n} (hax : a ≤ x)
    (hxb : x ≤ b) (h : blockIndex B a = blockIndex B b) :
    blockIndex B a = blockIndex B x :=
  le_antisymm (blockIndex_monotone B hax) ((blockIndex_monotone B hxb).trans_eq h.symm)

/-- The inverse order condition is the inclusion of the inverse descents in the cuts. -/
theorem inverseIncreasing_iff (C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    SourceIncreasing C w.symm ↔ ∀ e ∈ permutationDescents w.symm, e ∈ C.cuts := by
  unfold SourceIncreasing
  rw [strictMono_blocks_iff_descents]
  refine forall₂_congr fun e _ => ?_
  exact (not_congr (blockIndex_lo_eq_hi_iff C e)).trans not_not

/-- A transposition preserves the blocks exactly when it swaps two coordinates of one block. -/
theorem swap_mem_blockWeyl_iff (B : BlockShape n) (a b : Fin n) :
    Equiv.swap a b ∈ blockWeyl B ↔ blockIndex B a = blockIndex B b := by
  constructor
  · intro h
    have hs := h a
    rw [Equiv.swap_apply_left] at hs
    exact hs.symm
  · intro hab x
    by_cases hxa : x = a
    · subst x
      rw [Equiv.swap_apply_left]
      exact hab.symm
    by_cases hxb : x = b
    · subst x
      rw [Equiv.swap_apply_right]
      exact hab
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem mem_comap_conj_iff (C : BlockShape n) (w u : Equiv.Perm (Fin n)) :
    u ∈ (blockWeyl C).comap (MulAut.conj w).toMonoidHom ↔
      ∀ x, blockIndex C (w (u x)) = blockIndex C (w x) := by
  rw [Subgroup.mem_comap]
  change (∀ y, blockIndex C ((w * u * w⁻¹) y) = blockIndex C y) ↔ _
  constructor
  · intro h x
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using h (w x)
  · intro h y
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using
      h (w⁻¹ y)

/-- Equality of the actual source intersection with `W_K` is equality of the block
relations: `K` is the common refinement of `B` and the pullback of `C` along `w`. -/
theorem intersection_eq_iff (B C K : BlockShape n) (w : Equiv.Perm (Fin n)) :
    blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w).toMonoidHom = blockWeyl K ↔
      ∀ a b, blockIndex K a = blockIndex K b ↔
        blockIndex B a = blockIndex B b ∧ blockIndex C (w a) = blockIndex C (w b) := by
  constructor
  · intro h a b
    have hs : Equiv.swap a b ∈ blockWeyl K ↔
        Equiv.swap a b ∈ blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w).toMonoidHom := by
      rw [h]
    rw [Subgroup.mem_inf, swap_mem_blockWeyl_iff, swap_mem_blockWeyl_iff,
      mem_comap_conj_iff] at hs
    rw [hs]
    refine and_congr Iff.rfl ⟨fun hx => ?_, fun hab x => ?_⟩
    · have := hx a
      rw [Equiv.swap_apply_left] at this
      exact this.symm
    · by_cases hxa : x = a
      · subst x
        rw [Equiv.swap_apply_left]
        exact hab.symm
      by_cases hxb : x = b
      · subst x
        rw [Equiv.swap_apply_right]
        exact hab
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  · intro h
    ext u
    rw [Subgroup.mem_inf, mem_comap_conj_iff]
    change ((∀ x, blockIndex B (u x) = blockIndex B x) ∧ _) ↔
      ∀ x, blockIndex K (u x) = blockIndex K x
    constructor
    · rintro ⟨h1, h2⟩ x
      exact (h (u x) x).mpr ⟨h1 x, h2 x⟩
    · intro hk
      exact ⟨fun x => ((h (u x) x).mp (hk x)).1, fun x => ((h (u x) x).mp (hk x)).2⟩

/-- A discrete intermediate value step. -/
theorem exists_step {P : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : P a) (hb : ¬P b) :
    ∃ i, a ≤ i ∧ i < b ∧ P i ∧ ¬P (i + 1) := by
  induction b with
  | zero =>
    have h0 : a = 0 := Nat.le_zero.mp hab
    subst h0
    exact absurd ha hb
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · subst h
      exact absurd ha hb
    · by_cases hPb : P b
      · exact ⟨b, by omega, by omega, hPb, hb⟩
      · obtain ⟨i, h1, h2, h3, h4⟩ := ih (by omega) hPb
        exact ⟨i, h1, by omega, h3, h4⟩

/-- For an edge inside a source block, the two image coordinates lie in different target
blocks exactly when the images are adjacent across a target cut, or are not adjacent. -/
theorem not_sameBlock_iff (B C : BlockShape n) {w : Equiv.Perm (Fin n)}
    (hB : SourceIncreasing B w) (hC : SourceIncreasing C w.symm)
    (i : Fin (n - 1)) (hi : i ∉ B.cuts) :
    blockIndex C (w (edgeLo i)) ≠ blockIndex C (w (edgeHi i)) ↔
      ∀ e : Fin (n - 1), e.val = (w (edgeLo i)).val → e.val + 1 = (w (edgeHi i)).val →
        e ∈ C.cuts := by
  have hlt : w (edgeLo i) < w (edgeHi i) :=
    lt_of_sameBlock B hB (lo_lt_hi i) ((blockIndex_lo_eq_hi_iff B i).mpr hi)
  have hlt' := Fin.lt_def.mp hlt
  by_cases hadj : (w (edgeHi i)).val = (w (edgeLo i)).val + 1
  · let e : Fin (n - 1) := ⟨(w (edgeLo i)).val, by have := (w (edgeHi i)).isLt; omega⟩
    have hlo : edgeLo e = w (edgeLo i) := Fin.ext rfl
    have hhi : edgeHi e = w (edgeHi i) := Fin.ext hadj.symm
    constructor
    · intro hne e' he' _
      have he : e' = e := Fin.ext he'
      subst he
      by_contra hn
      apply hne
      rw [← hlo, ← hhi]
      exact (blockIndex_lo_eq_hi_iff C e).mpr hn
    · intro h heq
      have hm := h e rfl hadj.symm
      rw [← hlo, ← hhi] at heq
      exact ((blockIndex_lo_eq_hi_iff C e).mp heq) hm
  · constructor
    · intro _ e he1 he2
      exact absurd (by omega) hadj
    · intro _ heq
      have hz : (w (edgeLo i)).val + 1 < n := by have := (w (edgeHi i)).isLt; omega
      let z : Fin n := ⟨(w (edgeLo i)).val + 1, hz⟩
      have h1 : w (edgeLo i) < z := by
        rw [Fin.lt_def]
        change (w (edgeLo i)).val < (w (edgeLo i)).val + 1
        omega
      have h2 : z < w (edgeHi i) := by
        rw [Fin.lt_def]
        change (w (edgeLo i)).val + 1 < (w (edgeHi i)).val
        omega
      have hsz : blockIndex C (w (edgeLo i)) = blockIndex C z :=
        blockIndex_eq_of_between C h1.le h2.le heq
      have k1 := lt_of_sameBlock C hC h1 hsz
      have k2 := lt_of_sameBlock C hC h2 (hsz.symm.trans heq)
      rw [Equiv.symm_apply_apply] at k1
      rw [Equiv.symm_apply_apply] at k2
      rw [Fin.lt_def, val_lo] at k1
      rw [Fin.lt_def, val_hi] at k2
      omega

/-- The cut sets of target shapes that contribute for a fixed permutation `w`: the source
order condition, the inverse descents are cuts, and on every source-block edge the target
cut at the image edge records the intersection cut. -/
def Admissible (B K : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : Finset (Fin (n - 1))) : Prop :=
  SourceIncreasing B w ∧ (∀ e ∈ permutationDescents w.symm, e ∈ S) ∧
    ∀ i : Fin (n - 1), i ∉ B.cuts →
      (i ∈ K.cuts ↔ ∀ e : Fin (n - 1), e.val = (w (edgeLo i)).val →
        e.val + 1 = (w (edgeHi i)).val → e ∈ S)

/-- The two conditions in the coefficient are exactly admissibility of the target cuts. -/
theorem admissible_iff (B C K : BlockShape n) (hKB : B.cuts ⊆ K.cuts)
    (w : Equiv.Perm (Fin n)) :
    (IsMinimalRepresentative B C w ∧
      blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w).toMonoidHom = blockWeyl K) ↔
      Admissible B K w C.cuts := by
  rw [intersection_eq_iff]
  constructor
  · rintro ⟨⟨hB, hC⟩, hY⟩
    refine ⟨hB, (inverseIncreasing_iff C w).mp hC, fun i hi => ?_⟩
    rw [← not_sameBlock_iff B C hB hC i hi]
    have hBs : blockIndex B (edgeLo i) = blockIndex B (edgeHi i) :=
      (blockIndex_lo_eq_hi_iff B i).mpr hi
    have hK := hY (edgeLo i) (edgeHi i)
    rw [blockIndex_lo_eq_hi_iff K i] at hK
    constructor
    · intro hk hc
      exact (hK.mpr ⟨hBs, hc⟩) hk
    · intro hc
      by_contra hk
      exact hc (hK.mp hk).2
  · rintro ⟨hB, hD, hcl⟩
    have hC : SourceIncreasing C w.symm := (inverseIncreasing_iff C w).mpr hD
    refine ⟨⟨hB, hC⟩, ?_⟩
    have hadj : ∀ i : Fin (n - 1), i ∉ B.cuts →
        (i ∉ K.cuts ↔ blockIndex C (w (edgeLo i)) = blockIndex C (w (edgeHi i))) := by
      intro i hi
      exact (not_congr ((hcl i hi).trans (not_sameBlock_iff B C hB hC i hi).symm)).trans
        not_not
    have main : ∀ a b : Fin n, a ≤ b → (blockIndex K a = blockIndex K b ↔
        blockIndex B a = blockIndex B b ∧ blockIndex C (w a) = blockIndex C (w b)) := by
      intro a b hab
      constructor
      · intro hK
        have hK' := (blockIndex_eq_iff_cut_sides K a b).mp hK
        refine ⟨(blockIndex_eq_iff_cut_sides B a b).mpr fun i hi => hK' i (hKB hi), ?_⟩
        by_contra hne
        rw [blockIndex_eq_iff_cut_sides, not_forall] at hne
        obtain ⟨c, hc⟩ := hne
        obtain ⟨hc, hsep⟩ := not_imp.mp hc
        let P : ℕ → Prop := fun x => ∀ hx : x < n,
          ((w ⟨x, hx⟩).val ≤ c.val ↔ (w a).val ≤ c.val)
        have hPa : P a.val := fun hx => Iff.rfl
        have hPb : ¬P b.val := fun h => hsep (h b.isLt).symm
        obtain ⟨i, hai, hib, hPi, hPi1⟩ := exists_step (Fin.le_def.mp hab) hPa hPb
        have hin : i < n - 1 := lt_of_lt_of_le hib (Nat.le_sub_one_of_lt b.isLt)
        let e : Fin (n - 1) := ⟨i, hin⟩
        have hlo := hPi (edgeLo e).isLt
        have hhi : ¬((w (edgeHi e)).val ≤ c.val ↔ (w a).val ≤ c.val) := by
          intro h
          exact hPi1 fun hx => h
        clear hPi hPi1 hPa hPb
        have heK : e ∉ K.cuts := by
          intro he
          have hs := hK' e he
          change a.val ≤ i ↔ b.val ≤ i at hs
          omega
        have hsame := (hadj e fun he => heK (hKB he)).mp heK
        have hs := (blockIndex_eq_iff_cut_sides C _ _).mp hsame c hc
        exact hhi (hs.symm.trans hlo)
      · rintro ⟨hBab, hCab⟩
        apply (blockIndex_eq_iff_cut_sides K a b).mpr
        intro e he
        by_contra hne
        have hav := Fin.le_def.mp hab
        have hae : a.val ≤ e.val := by omega
        have heb : e.val < b.val := by omega
        have heB : e ∉ B.cuts := by
          intro hb
          have hs := (blockIndex_eq_iff_cut_sides B a b).mp hBab e hb
          exact hne hs
        have hnot := mt (hadj e heB).mpr (not_not.mpr he)
        apply hnot
        have hal : a ≤ edgeLo e := Fin.le_def.mpr (by simpa using hae)
        have hlh : edgeLo e ≤ edgeHi e := (lo_lt_hi e).le
        have hhb : edgeHi e ≤ b := Fin.le_def.mpr (by simpa using heb)
        have hBl := blockIndex_eq_of_between B hal (hlh.trans hhb) hBab
        have hBh := blockIndex_eq_of_between B (hal.trans hlh) hhb hBab
        have w1 := le_of_sameBlock B hB hal hBl
        have w2 := le_of_sameBlock B hB hlh (hBl.symm.trans hBh)
        have w3 := le_of_sameBlock B hB hhb (hBh.symm.trans hBab)
        have c1 := blockIndex_monotone C w1
        have c2 := blockIndex_monotone C w2
        have c3 := blockIndex_monotone C w3
        exact le_antisymm c2 (c3.trans (hCab.symm.le.trans c1))
    intro a b
    rcases le_total a b with hab | hba
    · exact main a b hab
    · have h := main b a hba
      constructor
      · intro hk
        obtain ⟨h1, h2⟩ := h.mp hk.symm
        exact ⟨h1.symm, h2.symm⟩
      · rintro ⟨h1, h2⟩
        exact (h.mpr ⟨h1.symm, h2.symm⟩).symm

theorem neg_one_pow_card_compl_symmDiff {m : ℕ} (S : Finset (Fin m)) (e : Fin m) :
    (-1 : ℤ) ^ (symmDiff S {e})ᶜ.card = -(-1 : ℤ) ^ Sᶜ.card := by
  have hc : (symmDiff S {e})ᶜ = symmDiff Sᶜ {e} := by
    ext x
    simp only [Finset.mem_compl, Finset.mem_symmDiff, Finset.mem_singleton]
    tauto
  rw [hc]
  by_cases h : e ∈ Sᶜ
  · have h1 : symmDiff Sᶜ {e} = Sᶜ.erase e := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (⟨hx, hne⟩ | ⟨rfl, hx⟩)
        · exact ⟨hne, hx⟩
        · exact absurd h hx
      · rintro ⟨hne, hx⟩
        exact Or.inl ⟨hx, hne⟩
    rw [h1, ← Finset.card_erase_add_one h, pow_succ]
    ring
  · have h1 : symmDiff Sᶜ {e} = insert e Sᶜ := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro (⟨hx, _⟩ | ⟨rfl, _⟩)
        · exact Or.inr hx
        · exact Or.inl rfl
      · rintro (rfl | hx)
        · exact Or.inr ⟨rfl, h⟩
        · exact Or.inl ⟨hx, fun hxe => h (hxe ▸ hx)⟩
    rw [h1, Finset.card_insert_of_notMem h, pow_succ]
    ring

open Classical in
/-- A free edge, neither an inverse descent nor the image of a source-block edge, cancels
the signed sum over target cut sets by toggling. -/
theorem sum_eq_zero_of_free (B K : BlockShape n) (w : Equiv.Perm (Fin n))
    (e₀ : Fin (n - 1)) (hD : e₀ ∉ permutationDescents w.symm)
    (hP : ∀ i : Fin (n - 1), i ∉ B.cuts → e₀.val = (w (edgeLo i)).val →
      e₀.val + 1 ≠ (w (edgeHi i)).val) :
    (∑ S : Finset (Fin (n - 1)),
      if Admissible B K w S then (-1 : ℤ) ^ Sᶜ.card else 0) = 0 := by
  have hmem : ∀ (S : Finset (Fin (n - 1))) (e : Fin (n - 1)), e ≠ e₀ →
      (e ∈ symmDiff S {e₀} ↔ e ∈ S) := by
    intro S e he
    rw [Finset.mem_symmDiff, Finset.mem_singleton]
    tauto
  have hadm : ∀ S, Admissible B K w (symmDiff S {e₀}) ↔ Admissible B K w S := by
    intro S
    unfold Admissible
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · refine forall₂_congr fun e he => hmem S e ?_
      rintro rfl
      exact hD he
    · refine forall₂_congr fun i hi => iff_congr Iff.rfl
        (forall_congr' fun e => imp_congr_right fun h1 => imp_congr_right fun h2 =>
          hmem S e ?_)
      rintro rfl
      exact hP i hi h1 h2
  refine Finset.sum_ninvolution (fun S => symmDiff S {e₀}) ?_ ?_ ?_ ?_
  · intro S
    by_cases h : Admissible B K w S
    · rw [ite_eq_left h, ite_eq_left ((hadm S).mpr h), neg_one_pow_card_compl_symmDiff]
      ring
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hadm S).mp h'))]
      ring
  · intro S _ heq
    have h := congrArg (fun T => e₀ ∈ T) heq
    simp only [Finset.mem_symmDiff, Finset.mem_singleton] at h
    tauto
  · intro S
    exact Finset.mem_univ _
  · intro S
    exact symmDiff_symmDiff_cancel_right {e₀} S

/-- The sort key listing the source blocks in decreasing order, increasingly inside
each block. -/
def reversalKey (B : BlockShape n) (a : Fin n) : Lex ((Fin B.length)ᵒᵈ × Fin n) :=
  toLex (OrderDual.toDual (blockIndex B a), a)

theorem reversalKey_injective (B : BlockShape n) : Function.Injective (reversalKey B) := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  simpa [reversalKey] using this

theorem reversalKey_lt_iff (B : BlockShape n) (a b : Fin n) :
    reversalKey B a < reversalKey B b ↔
      blockIndex B b < blockIndex B a ∨ (blockIndex B a = blockIndex B b ∧ a < b) := by
  simp only [reversalKey, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual,
    OrderDual.toDual_inj]

/-- The block reversal: the source blocks in reverse order, each kept increasing. -/
def reversal (B : BlockShape n) : Equiv.Perm (Fin n) :=
  (Tuple.sort (reversalKey B)).symm

theorem reversal_lt_iff (B : BlockShape n) (x y : Fin n) :
    reversal B x < reversal B y ↔ reversalKey B x < reversalKey B y := by
  have hm : StrictMono (reversalKey B ∘ Tuple.sort (reversalKey B)) :=
    (Tuple.monotone_sort (reversalKey B)).strictMono_of_injective
      ((reversalKey_injective B).comp (Tuple.sort (reversalKey B)).injective)
  have h := hm.lt_iff_lt (a := reversal B x) (b := reversal B y)
  simpa [reversal] using h.symm

theorem reversal_sourceIncreasing (B : BlockShape n) : SourceIncreasing B (reversal B) := by
  intro j a b hab
  change reversal B (B.index j a) < reversal B (B.index j b)
  rw [reversal_lt_iff, reversalKey_lt_iff, blockIndex_index, blockIndex_index]
  exact Or.inr ⟨rfl, index_strictMono B j hab⟩

/-- The reversal sends every source-block edge to an adjacent pair. -/
theorem reversal_adjacent (B : BlockShape n) (i : Fin (n - 1)) (hi : i ∉ B.cuts) :
    (reversal B (edgeHi i)).val = (reversal B (edgeLo i)).val + 1 := by
  have hs := (blockIndex_lo_eq_hi_iff B i).mpr hi
  have hlt : reversal B (edgeLo i) < reversal B (edgeHi i) := by
    rw [reversal_lt_iff, reversalKey_lt_iff]
    exact Or.inr ⟨hs, lo_lt_hi i⟩
  have hlt' := Fin.lt_def.mp hlt
  by_contra hne
  have hv : (reversal B (edgeLo i)).val + 1 < n := by
    have := (reversal B (edgeHi i)).isLt
    omega
  let v : Fin n := ⟨(reversal B (edgeLo i)).val + 1, hv⟩
  have h1 : reversal B (edgeLo i) < reversal B ((reversal B).symm v) := by
    rw [Equiv.apply_symm_apply, Fin.lt_def]
    change (reversal B (edgeLo i)).val < (reversal B (edgeLo i)).val + 1
    omega
  have h2 : reversal B ((reversal B).symm v) < reversal B (edgeHi i) := by
    rw [Equiv.apply_symm_apply, Fin.lt_def]
    change (reversal B (edgeLo i)).val + 1 < (reversal B (edgeHi i)).val
    omega
  rw [reversal_lt_iff, reversalKey_lt_iff] at h1 h2
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · rw [hs] at h1
    exact lt_asymm h1 h2
  · rw [hs, ← h2] at h1
    exact lt_irrefl _ h1
  · rw [← h1, ← hs] at h2
    exact lt_irrefl _ h2
  · rw [Fin.lt_def, val_lo] at h1'
    rw [Fin.lt_def, val_hi] at h2'
    omega

/-- Every edge is an inverse descent of the reversal or the image of a source-block edge. -/
theorem reversal_no_free (B : BlockShape n) (e : Fin (n - 1)) :
    e ∈ permutationDescents (reversal B).symm ∨
      ∃ i : Fin (n - 1), i ∉ B.cuts ∧ e.val = (reversal B (edgeLo i)).val ∧
        e.val + 1 = (reversal B (edgeHi i)).val := by
  set x := (reversal B).symm (edgeLo e) with hx
  set y := (reversal B).symm (edgeHi e) with hy
  have hkey : reversalKey B x < reversalKey B y := by
    rw [← reversal_lt_iff, hx, hy, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact lo_lt_hi e
  rw [reversalKey_lt_iff] at hkey
  rcases hkey with hb | ⟨hb, hxy⟩
  · left
    rw [mem_descents_iff, ← hx, ← hy]
    by_contra hle
    exact (not_le_of_gt hb) (blockIndex_monotone B (le_of_not_gt hle))
  · right
    have hxy' := Fin.lt_def.mp hxy
    have hadj : y.val = x.val + 1 := by
      by_contra hne
      have hv : x.val + 1 < n := by
        have := y.isLt
        omega
      let v : Fin n := ⟨x.val + 1, hv⟩
      have h1 : x < v := by
        rw [Fin.lt_def]
        change x.val < x.val + 1
        omega
      have h2 : v < y := by
        rw [Fin.lt_def]
        change x.val + 1 < y.val
        omega
      have hxv := blockIndex_eq_of_between B h1.le h2.le hb
      have k1 : reversal B x < reversal B v := by
        rw [reversal_lt_iff, reversalKey_lt_iff]
        exact Or.inr ⟨hxv, h1⟩
      have k2 : reversal B v < reversal B y := by
        rw [reversal_lt_iff, reversalKey_lt_iff]
        exact Or.inr ⟨hxv.symm.trans hb, h2⟩
      rw [hx, Equiv.apply_symm_apply, Fin.lt_def, val_lo] at k1
      rw [hy, Equiv.apply_symm_apply, Fin.lt_def, val_hi] at k2
      omega
    have hxn : x.val < n - 1 := by
      have := y.isLt
      omega
    let i : Fin (n - 1) := ⟨x.val, hxn⟩
    have hli : edgeLo i = x := Fin.ext rfl
    have hhi : edgeHi i = y := Fin.ext hadj.symm
    refine ⟨i, ?_, ?_, ?_⟩
    · rw [← blockIndex_lo_eq_hi_iff, hli, hhi]
      exact hb
    · rw [hli, hx, Equiv.apply_symm_apply, val_lo]
    · rw [hhi, hy, Equiv.apply_symm_apply, val_hi]

/-- Monotonicity on `Fin n` is detected on adjacent coordinates. -/
theorem monotone_of_adjacent {α : Type*} [Preorder α] {f : Fin n → α}
    (h : ∀ e : Fin (n - 1), f (edgeLo e) ≤ f (edgeHi e)) : Monotone f := by
  cases n with
  | zero =>
    intro a
    exact Fin.elim0 a
  | succ m =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact h ⟨i.val, by omega⟩

/-- A source-increasing permutation without free edges is the block reversal. -/
theorem eq_reversal (B : BlockShape n) {w : Equiv.Perm (Fin n)} (hB : SourceIncreasing B w)
    (hfree : ∀ e : Fin (n - 1), e ∉ permutationDescents w.symm →
      ∃ i : Fin (n - 1), i ∉ B.cuts ∧ e.val = (w (edgeLo i)).val ∧
        e.val + 1 = (w (edgeHi i)).val) :
    w = reversal B := by
  have hs : w.symm = Tuple.sort (reversalKey B) := by
    rw [Tuple.eq_sort_iff]
    refine ⟨monotone_of_adjacent fun e => ?_, fun i j hij heq => ?_⟩
    · by_cases hd : e ∈ permutationDescents w.symm
      · rw [mem_descents_iff] at hd
        apply le_of_lt
        change reversalKey B (w.symm (edgeLo e)) < reversalKey B (w.symm (edgeHi e))
        rw [reversalKey_lt_iff]
        left
        rcases (blockIndex_monotone B hd.le).lt_or_eq with h | h
        · exact h
        · exfalso
          have hw := lt_of_sameBlock B hB hd h
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hw
          exact lt_asymm hw (lo_lt_hi e)
      · obtain ⟨i, hi, h1, h2⟩ := hfree e hd
        have hl : w.symm (edgeLo e) = edgeLo i := by
          rw [Equiv.symm_apply_eq]
          exact Fin.ext h1
        have hh : w.symm (edgeHi e) = edgeHi i := by
          rw [Equiv.symm_apply_eq]
          exact Fin.ext (by rw [val_hi]; exact h2)
        apply le_of_lt
        change reversalKey B (w.symm (edgeLo e)) < reversalKey B (w.symm (edgeHi e))
        rw [hl, hh, reversalKey_lt_iff]
        exact Or.inr ⟨(blockIndex_lo_eq_hi_iff B i).mpr hi, lo_lt_hi i⟩
    · exact absurd (w.symm.injective (reversalKey_injective B heq)) hij.ne
  rw [reversal, ← hs, Equiv.symm_symm]

open Classical in
/-- The block reversal contributes the single cut set whose uncut edges are the images of
the uncut edges of `K`. -/
theorem sum_reversal (B K : BlockShape n) (hKB : B.cuts ⊆ K.cuts) :
    (∑ S : Finset (Fin (n - 1)),
      if Admissible B K (reversal B) S then (-1 : ℤ) ^ Sᶜ.card else 0) =
        (-1 : ℤ) ^ K.uncuts.card := by
  set w := reversal B with hw
  let T : Finset (Fin (n - 1)) :=
    Finset.univ.filter fun e => ∃ i : Fin (n - 1), i ∉ K.cuts ∧ e.val = (w (edgeLo i)).val
  have hmemT : ∀ e, e ∈ T ↔ ∃ i : Fin (n - 1), i ∉ K.cuts ∧ e.val = (w (edgeLo i)).val := by
    intro e
    simp [T]
  have hadjK : ∀ i : Fin (n - 1), i ∉ K.cuts → (w (edgeHi i)).val = (w (edgeLo i)).val + 1 :=
    fun i hi => reversal_adjacent B i fun h => hi (hKB h)
  have hiff : ∀ S, Admissible B K w S ↔ S = Tᶜ := by
    intro S
    constructor
    · rintro ⟨_, hD, hcl⟩
      ext e
      rw [Finset.mem_compl, hmemT]
      constructor
      · rintro he ⟨i, hik, hei⟩
        have hiB : i ∉ B.cuts := fun h => hik (hKB h)
        have h := mt (hcl i hiB).mpr hik
        push Not at h
        obtain ⟨e', he'1, _, he'3⟩ := h
        have : e' = e := Fin.ext (he'1.trans hei.symm)
        exact he'3 (this ▸ he)
      · intro hnot
        rcases reversal_no_free B e with hd | ⟨i, hiB, h1, h2⟩
        · exact hD e hd
        · have hik : i ∈ K.cuts := by
            by_contra hik
            exact hnot ⟨i, hik, h1⟩
          exact (hcl i hiB).mp hik e h1 h2
    · rintro rfl
      refine ⟨reversal_sourceIncreasing B, fun e hd => ?_, fun i hiB => ?_⟩
      · rw [Finset.mem_compl, hmemT]
        rintro ⟨i, hik, hei⟩
        have hadj := hadjK i hik
        have hl : w.symm (edgeLo e) = edgeLo i := by
          rw [Equiv.symm_apply_eq]
          exact Fin.ext hei
        have hh : w.symm (edgeHi e) = edgeHi i := by
          rw [Equiv.symm_apply_eq]
          exact Fin.ext (by rw [val_hi, hadj, hei])
        rw [mem_descents_iff, hl, hh] at hd
        exact lt_asymm hd (lo_lt_hi i)
      · constructor
        · intro hik e he1 _
          rw [Finset.mem_compl, hmemT]
          rintro ⟨i', hik', he'⟩
          have hw' : w (edgeLo i') = w (edgeLo i) := Fin.ext (he'.symm.trans he1)
          have : i' = i := lo_injective (w.injective hw')
          exact hik' (this ▸ hik)
        · intro h
          by_contra hik
          have hadj := hadjK i hik
          have hb : (w (edgeLo i)).val < n - 1 := by
            have := (w (edgeHi i)).isLt
            omega
          have hm := h ⟨(w (edgeLo i)).val, hb⟩ rfl hadj.symm
          rw [Finset.mem_compl, hmemT] at hm
          exact hm ⟨i, hik, rfl⟩
  have hcard : T.card = K.uncuts.card := by
    symm
    refine Finset.card_bij (fun i hi => ⟨(w (edgeLo i)).val, ?_⟩) ?_ ?_ ?_
    · have hik : i ∉ K.cuts := (BlockShape.mem_uncuts_iff K i).mp hi
      have hadj := hadjK i hik
      have := (w (edgeHi i)).isLt
      omega
    · intro i hi
      rw [hmemT]
      exact ⟨i, (BlockShape.mem_uncuts_iff K i).mp hi, rfl⟩
    · intro i₁ _ i₂ _ h
      have hv := congrArg Fin.val h
      exact lo_injective (w.injective (Fin.ext hv))
    · intro e he
      obtain ⟨i, hik, hei⟩ := (hmemT e).mp he
      exact ⟨i, (BlockShape.mem_uncuts_iff K i).mpr hik, Fin.ext hei.symm⟩
  rw [Finset.sum_eq_single Tᶜ]
  · rw [ite_eq_left ((hiff _).mpr rfl), compl_compl, hcard]
  · intro S _ hS
    rw [ite_eq_right fun h => hS ((hiff S).mp h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

open Classical in
/-- The coefficient as a sum of indicator values over all permutations. -/
theorem natCard_eq_sum (B C K : BlockShape n) (hKB : B.cuts ⊆ K.cuts) :
    (Nat.card {w : MinimalRepresentatives B C //
      blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w.val).toMonoidHom =
        blockWeyl K} : ℤ) =
      ∑ w : Equiv.Perm (Fin n), if Admissible B K w C.cuts then (1 : ℤ) else 0 := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun w => IsMinimalRepresentative B C w)
      (fun w => blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w).toMonoidHom =
        blockWeyl K)),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : Admissible B K w C.cuts
  · rw [ite_eq_left ((admissible_iff B C K hKB w).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((admissible_iff B C K hKB w).mp h')), ite_eq_right h]

end TypeASolomon

open TypeASolomon in
open Classical in
/-- The signed type-A Solomon coefficient identity for actual block Weyl intersections. -/
theorem typeASolomonCoefficientStatement : TypeASolomonCoefficientStatement := by
  intro n B K hKB
  let _ : Fintype (BlockShape n) := Fintype.ofFinite (BlockShape n)
  have hcuts := (blockWeyl_le_iff_cuts_subset B K).mp hKB
  calc (∑ C : BlockShape n, ((-1 : ℤ) ^ (n - C.length)) *
        (Nat.card {w : MinimalRepresentatives B C //
          blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w.val).toMonoidHom =
            blockWeyl K} : ℤ))
      = ∑ C : BlockShape n, ∑ w : Equiv.Perm (Fin n),
          if Admissible B K w C.cuts then (-1 : ℤ) ^ C.cutsᶜ.card else 0 := by
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [natCard_eq_sum B C K hcuts, Finset.mul_sum, C.sign_eq_pow_uncuts_card,
          BlockShape.uncuts, ← Finset.compl_eq_univ_sdiff]
        refine Finset.sum_congr rfl fun w _ => ?_
        split_ifs <;> ring
    _ = ∑ w : Equiv.Perm (Fin n), ∑ C : BlockShape n,
          if Admissible B K w C.cuts then (-1 : ℤ) ^ C.cutsᶜ.card else 0 :=
        Finset.sum_comm
    _ = ∑ w : Equiv.Perm (Fin n), ∑ S : Finset (Fin (n - 1)),
          if Admissible B K w S then (-1 : ℤ) ^ Sᶜ.card else 0 := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact Fintype.sum_equiv (BlockShape.cutEquiv n) _ _ fun C => rfl
    _ = ∑ S : Finset (Fin (n - 1)),
          if Admissible B K (reversal B) S then (-1 : ℤ) ^ Sᶜ.card else 0 := by
        refine Finset.sum_eq_single (reversal B) (fun w _ hw => ?_) (fun h => ?_)
        · by_cases hB : SourceIncreasing B w
          · have hfree : ∃ e₀ : Fin (n - 1), e₀ ∉ permutationDescents w.symm ∧
                ∀ i : Fin (n - 1), i ∉ B.cuts → e₀.val = (w (edgeLo i)).val →
                  e₀.val + 1 ≠ (w (edgeHi i)).val := by
              by_contra hno
              push Not at hno
              exact hw (eq_reversal B hB hno)
            obtain ⟨e₀, hD, hP⟩ := hfree
            exact sum_eq_zero_of_free B K w e₀ hD hP
          · exact Finset.sum_eq_zero fun S _ => ite_eq_right fun h => hB h.1
        · exact absurd (Finset.mem_univ _) h
    _ = (-1 : ℤ) ^ K.uncuts.card := sum_reversal B K hcuts
    _ = (-1 : ℤ) ^ (n - K.length) := K.sign_eq_pow_uncuts_card.symm

end Langlands.Geometric
