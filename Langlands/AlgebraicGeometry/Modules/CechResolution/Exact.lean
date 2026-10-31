import Langlands.AlgebraicGeometry.Modules.CechResolution.Complex
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Interval.Finset.Fin

/-!
# Exactness of the sheafified Čech complex

The augmented sheafified alternating Čech complex `M ⟶ C⁰ ⟶ C¹ ⟶ ⋯` of an ordered affine cover
is exact. Exactness is local: over an open `W ⊆ 𝒰.U k` the alternating Čech complex of sections
has the contracting homotopy `(h c)(s) = (-1)^{#{i | s i < k}} c(s ∪ {k})` for `k ∉ s` and
`(h c)(s) = 0` otherwise. The augmentation is a monomorphism by the sheaf axiom. Consequently
`cechAug 𝒰 M` is a quasi-isomorphism.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

section Combinatorics

variable {ι : Type*} [LinearOrder ι]

/-- The number of entries of `s` strictly below `k`. -/
def pos {n : ℕ} (s : Fin n → ι) (k : ι) : ℕ :=
  (Finset.univ.filter fun i => s i < k).card

lemma pos_le {n : ℕ} (s : Fin n → ι) (k : ι) : pos s k ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_fin n).le

lemma lt_pos_iff {n : ℕ} {s : Fin n → ι} (hs : Monotone s) (k : ι) (i : Fin n) :
    (i : ℕ) < pos s k ↔ s i < k := by
  constructor
  · intro h
    by_contra hk
    have hsub : (Finset.univ.filter fun j => s j < k) ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hk (lt_of_le_of_lt (hs (not_lt.1 hji)) hj.2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    exact absurd h (not_lt.2 this)
  · intro h
    have hsub : Finset.Iic i ⊆ (Finset.univ.filter fun j => s j < k) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, lt_of_le_of_lt (hs hj) h⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    exact this

lemma pos_eq {n : ℕ} {s : Fin n → ι} (hs : Monotone s) {k : ι} {P : ℕ} (hP : P ≤ n)
    (h : ∀ i : Fin n, (i : ℕ) < P ↔ s i < k) : pos s k = P := by
  have h' : ∀ i : Fin n, (i : ℕ) < pos s k ↔ (i : ℕ) < P :=
    fun i => (lt_pos_iff hs k i).trans (h i).symm
  rcases lt_trichotomy (pos s k) P with hlt | heq | hgt
  · exact absurd ((h' ⟨pos s k, lt_of_lt_of_le hlt hP⟩).2 hlt) (lt_irrefl _)
  · exact heq
  · exact absurd ((h' ⟨P, lt_of_lt_of_le hgt (pos_le s k)⟩).1 hgt) (lt_irrefl _)

lemma val_succAbove {n : ℕ} (a : Fin (n + 1)) (i : Fin n) :
    ((a.succAbove i : Fin (n + 1)) : ℕ) = if (i : ℕ) < (a : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  simp only [Fin.succAbove]
  split_ifs <;> simp_all [Fin.lt_def]

end Combinatorics

variable {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover)

section Idx

lemma idx_ext_range {p : ℕ} {s s' : 𝒰.Idx p} (h : Set.range s.1 = Set.range s'.1) : s = s' :=
  Subtype.ext ((s.2.range_inj_of_wellFoundedLT s'.2).1 h)

lemma range_face {p : ℕ} (t : 𝒰.Idx (p + 1)) (j : Fin (p + 2)) :
    Set.range (𝒰.face t j).1 = Set.range t.1 \ {t.1 j} := by
  rw [𝒰.face_val, Set.range_comp, Fin.range_succAbove,
    Set.image_compl_eq_range_sdiff_image t.2.injective, Set.image_singleton]

/-- The position `#{i | s i < k}` at which `k` is inserted into `s`. -/
def insPos {p : ℕ} (s : 𝒰.Idx p) (k : 𝒰.ι) : Fin (p + 2) :=
  ⟨pos s.1 k, Nat.lt_succ_of_le (pos_le s.1 k)⟩

/-- The strictly increasing tuple obtained by inserting `k ∉ s` into `s`. -/
def insIdx {p : ℕ} (s : 𝒰.Idx p) (k : 𝒰.ι) (hk : k ∉ Set.range s.1) : 𝒰.Idx (p + 1) :=
  ⟨Fin.insertNth (α := fun _ => 𝒰.ι) (insPos 𝒰 s k) k s.1, by
    rw [Fin.strictMono_insertNth_iff]
    refine ⟨s.2, fun i hi => (lt_pos_iff s.2.monotone k i).1 hi, fun i hi => ?_⟩
    refine lt_of_le_of_ne (not_lt.1 fun h => ?_) fun h => hk ⟨i, h.symm⟩
    exact absurd ((lt_pos_iff s.2.monotone k i).2 h) (not_lt.2 hi)⟩

variable {𝒰}

lemma insIdx_apply_succAbove {p : ℕ} (s : 𝒰.Idx p) (k : 𝒰.ι) (hk : k ∉ Set.range s.1)
    (i : Fin (p + 1)) : (insIdx 𝒰 s k hk).1 ((insPos 𝒰 s k).succAbove i) = s.1 i := by
  simp only [insIdx]
  exact Fin.insertNth_apply_succAbove _ _ _ _

lemma range_insIdx {p : ℕ} (s : 𝒰.Idx p) (k : 𝒰.ι) (hk : k ∉ Set.range s.1) :
    Set.range (insIdx 𝒰 s k hk).1 = insert k (Set.range s.1) :=
  Fin.range_insertNth _ _ _

lemma face_insIdx {p : ℕ} (s : 𝒰.Idx p) (k : 𝒰.ι) (hk : k ∉ Set.range s.1) :
    𝒰.face (insIdx 𝒰 s k hk) (insPos 𝒰 s k) = s :=
  Subtype.ext (funext fun i => insIdx_apply_succAbove s k hk i)

lemma notMem_range_face {p : ℕ} {t : 𝒰.Idx (p + 1)} {k : 𝒰.ι} (hk : k ∉ Set.range t.1)
    (j : Fin (p + 2)) : k ∉ Set.range (𝒰.face t j).1 := by
  rw [range_face]
  exact fun h => hk h.1

lemma face_insIdx_succAbove {p : ℕ} (t : 𝒰.Idx (p + 1)) (k : 𝒰.ι) (hk : k ∉ Set.range t.1)
    (j : Fin (p + 2)) :
    𝒰.face (insIdx 𝒰 t k hk) ((insPos 𝒰 t k).succAbove j) =
      insIdx 𝒰 (𝒰.face t j) k (notMem_range_face hk j) := by
  apply idx_ext_range
  rw [range_face, range_insIdx, range_insIdx, range_face, insIdx_apply_succAbove]
  exact (Set.insert_sdiff_singleton_comm (fun h => hk ⟨j, h.symm⟩) _).symm

lemma self_notMem_range_face {p : ℕ} (t : 𝒰.Idx (p + 1)) (m : Fin (p + 2)) :
    t.1 m ∉ Set.range (𝒰.face t m).1 := by
  rw [range_face]
  exact fun h => h.2 rfl

lemma self_mem_range_face {p : ℕ} (t : 𝒰.Idx (p + 1)) {m j : Fin (p + 2)} (h : j ≠ m) :
    t.1 m ∈ Set.range (𝒰.face t j).1 := by
  rw [range_face]
  exact ⟨Set.mem_range_self _, fun e => h (t.2.injective e).symm⟩

lemma insIdx_face_self {p : ℕ} (t : 𝒰.Idx (p + 1)) (m : Fin (p + 2)) :
    insIdx 𝒰 (𝒰.face t m) (t.1 m) (self_notMem_range_face t m) = t := by
  apply idx_ext_range
  rw [range_insIdx, range_face, Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem (Set.mem_range_self _)]

lemma pos_face_self {p : ℕ} (t : 𝒰.Idx (p + 1)) (m : Fin (p + 2)) :
    pos (𝒰.face t m).1 (t.1 m) = m := by
  refine pos_eq (𝒰.face t m).2.monotone (Nat.lt_succ_iff.1 m.2) fun i => ?_
  rw [𝒰.face_val, Function.comp_apply, t.2.lt_iff_lt, Fin.succAbove_lt_iff_castSucc_lt,
    Fin.lt_def, Fin.val_castSucc]

lemma pos_face {p : ℕ} (t : 𝒰.Idx (p + 1)) (k : 𝒰.ι) (j : Fin (p + 2)) :
    pos (𝒰.face t j).1 k = if (j : ℕ) < pos t.1 k then pos t.1 k - 1 else pos t.1 k := by
  have hm := pos_le t.1 k
  have hj := j.2
  refine pos_eq (𝒰.face t j).2.monotone ?_ fun i => ?_
  · split_ifs <;> omega
  · rw [𝒰.face_val, Function.comp_apply, ← lt_pos_iff t.2.monotone, val_succAbove]
    have hi := i.2
    split_ifs <;> constructor <;> intro <;> omega

lemma sign_face {p : ℕ} (t : 𝒰.Idx (p + 1)) (k : 𝒰.ι) (j : Fin (p + 2)) :
    (j : ℕ) + pos (𝒰.face t j).1 k + 1 = pos t.1 k + ((insPos 𝒰 t k).succAbove j : ℕ) := by
  have hpos : ((insPos 𝒰 t k) : ℕ) = pos t.1 k := rfl
  rw [pos_face, val_succAbove, hpos]
  split_ifs <;> omega

/-- The one-element tuple `(i)`. -/
def single (i : 𝒰.ι) : 𝒰.Idx 0 :=
  ⟨fun _ => i, fun a b h => absurd h (by
    have ha := a.2
    have hb := b.2
    rw [show a = b from Fin.ext (by omega)]
    exact lt_irrefl b)⟩

lemma idx_zero_eq_single {s : 𝒰.Idx 0} {k : 𝒰.ι} (hk : k ∈ Set.range s.1) : s = single k := by
  obtain ⟨i, hi⟩ := hk
  exact Subtype.ext (funext fun i' => by
    have hi' := i'.2
    have hi2 := i.2
    rw [show i' = i from Fin.ext (by omega)]
    exact hi)

lemma face_insIdx_zero (s : 𝒰.Idx 0) (k : 𝒰.ι) (hk : k ∉ Set.range s.1) :
    𝒰.face (insIdx 𝒰 s k hk) ((insPos 𝒰 s k).succAbove 0) = single k := by
  apply idx_ext_range
  have hs : Set.range s.1 = {s.1 0} := by
    ext x
    refine ⟨fun ⟨i, hi⟩ => ?_, fun h => ⟨0, h.symm⟩⟩
    have hi' := i.2
    rw [Set.mem_singleton_iff, ← hi, show i = 0 from Fin.ext (by simp)]
  have hk' : k ≠ s.1 0 := fun h => hk ⟨0, h.symm⟩
  rw [range_face, range_insIdx, insIdx_apply_succAbove, hs,
    ← Set.insert_sdiff_singleton_comm hk', sdiff_self, Set.bot_eq_empty, insert_empty_eq]
  exact Set.range_const.symm

end Idx

section Sections

variable (M : X.Modules)

/-- The open `𝒰.inter s ⊓ W` (written as an image of a preimage) carrying the `s`-component of a
section over `W` of the Čech complex. -/
abbrev cechOpen {p : ℕ} (s : 𝒰.Idx p) (W : X.Opens) : X.Opens :=
  (𝒰.inter s).ι ''ᵁ ((𝒰.inter s).ι ⁻¹ᵁ W)

lemma cechOpen_eq {p : ℕ} (s : 𝒰.Idx p) (W : X.Opens) : cechOpen 𝒰 s W = 𝒰.inter s ⊓ W :=
  image_preimage_eq _ _

variable {𝒰} in
lemma cechOpen_le_of_range {p q : ℕ} {s : 𝒰.Idx p} {s' : 𝒰.Idx q} {k : 𝒰.ι} {W : X.Opens}
    (hW : W ≤ 𝒰.U k) (h : Set.range s'.1 ⊆ insert k (Set.range s.1)) :
    cechOpen 𝒰 s W ≤ cechOpen 𝒰 s' W := by
  rw [cechOpen_eq, cechOpen_eq]
  refine le_inf (le_iInf fun j => ?_) inf_le_right
  rcases Set.mem_insert_iff.1 (h ⟨j, rfl⟩) with hj | ⟨i, hi⟩
  · rw [hj]
    exact inf_le_right.trans hW
  · rw [← hi]
    exact inf_le_left.trans (𝒰.inter_le s i)

/-- Families of sections `s ↦ c s ∈ M(𝒰.inter s ⊓ W)`: the sections over `W` of the `p`-th
term of the sheafified Čech complex. -/
abbrev Sec (p : ℕ) (W : X.Opens) : Type u := ∀ s : 𝒰.Idx p, Γ(M, cechOpen 𝒰 s W)

variable {𝒰 M}

/-- The restriction of the `s`-component of `c` to a smaller open. -/
def cr {p : ℕ} {W : X.Opens} (c : Sec 𝒰 M p W) (s : 𝒰.Idx p) {W' : X.Opens}
    (h : W' ≤ cechOpen 𝒰 s W) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op (c s)

lemma cr_def {p : ℕ} {W : X.Opens} (c : Sec 𝒰 M p W) (s : 𝒰.Idx p) {W' : X.Opens}
    (h : W' ≤ cechOpen 𝒰 s W) : cr c s h = M.presheaf.map (homOfLE h).op (c s) := rfl

lemma cr_congr {p : ℕ} {W : X.Opens} (c : Sec 𝒰 M p W) {s s' : 𝒰.Idx p} (e : s = s')
    {W' : X.Opens} (h : W' ≤ cechOpen 𝒰 s W) (h' : W' ≤ cechOpen 𝒰 s' W) :
    cr c s h = cr c s' h' := by
  subst e
  rfl

lemma map_cr {p : ℕ} {W : X.Opens} (c : Sec 𝒰 M p W) (s : 𝒰.Idx p) {W' W'' : X.Opens}
    (h : W' ≤ cechOpen 𝒰 s W) (h' : W'' ≤ W') :
    M.presheaf.map (homOfLE h').op (cr c s h) = cr c s (h'.trans h) := by
  rw [cr_def, cr_def, ← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

lemma cr_self {p : ℕ} {W : X.Opens} (c : Sec 𝒰 M p W) (s : 𝒰.Idx p) :
    cr c s le_rfl = c s := by
  rw [cr_def, show (homOfLE (le_refl (cechOpen 𝒰 s W))).op = 𝟙 _ from rfl, M.presheaf.map_id]
  rfl

/-- The alternating Čech differential on families of sections. -/
def dSec {p : ℕ} {W : X.Opens} (c : Sec 𝒰 M p W) : Sec 𝒰 M (p + 1) W := fun t =>
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    cr c (𝒰.face t j) (image_preimage_mono (𝒰.inter_le_inter_face t j) W)

/-- The augmentation on families of sections: restriction from `W` to each `𝒰.U i ⊓ W`. -/
def aug0 {W : X.Opens} (m : Γ(M, W)) : Sec 𝒰 M 0 W := fun s =>
  M.presheaf.map (homOfLE ((𝒰.inter s).ι.image_preimage_le W)).op m

variable (k : 𝒰.ι) {W : X.Opens} (hW : W ≤ 𝒰.U k)

include hW in
lemma cechOpen_le_insIdx {p : ℕ} (s : 𝒰.Idx p) (hk : k ∉ Set.range s.1) :
    cechOpen 𝒰 s W ≤ cechOpen 𝒰 (insIdx 𝒰 s k hk) W :=
  cechOpen_le_of_range hW (range_insIdx s k hk).subset

include hW in
lemma le_cechOpen_single : W ≤ cechOpen 𝒰 (single k) W := by
  rw [cechOpen_eq]
  exact le_inf (hW.trans (le_iInf fun _ => le_rfl)) le_rfl

/-- The contracting homotopy over `W ≤ 𝒰.U k`. -/
def contr {p : ℕ} (c : Sec 𝒰 M (p + 1) W) : Sec 𝒰 M p W := fun s =>
  if hk : k ∈ Set.range s.1 then 0 else
    ((-1 : ℤ) ^ pos s.1 k) • cr c (insIdx 𝒰 s k hk) (cechOpen_le_insIdx k hW s hk)

lemma contr_of_mem {p : ℕ} (c : Sec 𝒰 M (p + 1) W) {s : 𝒰.Idx p} (hk : k ∈ Set.range s.1) :
    contr k hW c s = 0 := by
  simp [contr, hk]

lemma contr_of_notMem {p : ℕ} (c : Sec 𝒰 M (p + 1) W) {s : 𝒰.Idx p} (hk : k ∉ Set.range s.1) :
    contr k hW c s =
      ((-1 : ℤ) ^ pos s.1 k) • cr c (insIdx 𝒰 s k hk) (cechOpen_le_insIdx k hW s hk) := by
  simp [contr, hk]

include hW in
/-- The cocycle condition of `c` at `t ∪ {k}`, restricted to `𝒰.inter t ⊓ W`. -/
lemma cocycle_insIdx {p : ℕ} (c : Sec 𝒰 M p W) (hc : dSec c = 0) (t : 𝒰.Idx p)
    (hk : k ∉ Set.range t.1) :
    ((-1 : ℤ) ^ pos t.1 k) • c t + ∑ j : Fin (p + 1),
      ((-1 : ℤ) ^ ((insPos 𝒰 t k).succAbove j : ℕ)) •
        cr c (𝒰.face (insIdx 𝒰 t k hk) ((insPos 𝒰 t k).succAbove j))
          ((cechOpen_le_insIdx k hW t hk).trans
            (image_preimage_mono (𝒰.inter_le_inter_face _ _) W)) = 0 := by
  have h := congrArg (fun z => M.presheaf.map (homOfLE (cechOpen_le_insIdx k hW t hk)).op z)
    (congrFun hc (insIdx 𝒰 t k hk))
  simp only [Pi.zero_apply, map_zero, dSec] at h
  rw [map_sum, Fin.sum_univ_succAbove _ (insPos 𝒰 t k)] at h
  simp only [map_zsmul, map_cr] at h
  rw [cr_congr c (face_insIdx t k hk) _ le_rfl, cr_self] at h
  exact h

lemma sign_mul_self (n : ℕ) : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

lemma eq_of_sign_add_eq_one {A : Type*} [AddCommGroup A] {a b : ℕ} (hab : a + b = 1) {x y : A}
    (h : ((-1 : ℤ) ^ a) • x + ((-1 : ℤ) ^ b) • y = 0) : x = y := by
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · obtain rfl : b = 1 := by omega
    simp only [pow_zero, pow_one, one_smul, neg_smul] at h
    exact add_neg_eq_zero.1 h
  · obtain rfl : b = 0 := by omega
    simp only [pow_zero, pow_one, one_smul, neg_smul] at h
    exact neg_add_eq_zero.1 h

include hW in
/-- Exactness of the section complex over `W ≤ 𝒰.U k` in positive degrees. -/
theorem dSec_contr {p : ℕ} (c : Sec 𝒰 M (p + 1) W) (hc : dSec c = 0) :
    dSec (contr k hW c) = c := by
  funext t
  by_cases hk : k ∈ Set.range t.1
  · obtain ⟨m, rfl⟩ := hk
    simp only [dSec]
    rw [Finset.sum_eq_single m]
    · rw [cr_def (contr _ hW c), contr_of_notMem _ hW c (self_notMem_range_face t m), map_zsmul,
        map_cr, smul_smul, cr_congr c (insIdx_face_self t m) _ le_rfl, cr_self, pos_face_self,
        sign_mul_self, one_smul]
    · intro j _ hj
      rw [cr_def (contr _ hW c), contr_of_mem _ hW c (self_mem_range_face t hj), map_zero,
        smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have key : ∀ j : Fin (p + 2),
        cr (contr k hW c) (𝒰.face t j) (image_preimage_mono (𝒰.inter_le_inter_face t j) W) =
          ((-1 : ℤ) ^ pos (𝒰.face t j).1 k) •
            cr c (𝒰.face (insIdx 𝒰 t k hk) ((insPos 𝒰 t k).succAbove j))
              ((cechOpen_le_insIdx k hW t hk).trans
                (image_preimage_mono (𝒰.inter_le_inter_face _ _) W)) := by
      intro j
      rw [cr_def (contr k hW c), contr_of_notMem k hW c (notMem_range_face hk j), map_zsmul,
        map_cr, cr_congr c (face_insIdx_succAbove t k hk j).symm _
          ((cechOpen_le_insIdx k hW t hk).trans
            (image_preimage_mono (𝒰.inter_le_inter_face _ _) W))]
    have h := cocycle_insIdx k hW c hc t hk
    set S := ∑ j : Fin (p + 2), ((-1 : ℤ) ^ ((insPos 𝒰 t k).succAbove j : ℕ)) •
        cr c (𝒰.face (insIdx 𝒰 t k hk) ((insPos 𝒰 t k).succAbove j))
          ((cechOpen_le_insIdx k hW t hk).trans
            (image_preimage_mono (𝒰.inter_le_inter_face _ _) W)) with hS
    have hct : c t = ((-1 : ℤ) ^ pos t.1 k) • -S := by
      rw [← eq_neg_of_add_eq_zero_left h, smul_smul, sign_mul_self, one_smul]
    rw [hct]
    simp only [dSec]
    rw [hS, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key, smul_smul, smul_smul, ← neg_smul]
    congr 1
    rw [← pow_add, ← pow_add, ← sign_face]
    ring

include hW in
/-- Exactness of the augmented section complex over `W ≤ 𝒰.U k` in degree zero. -/
theorem aug0_cr_single (c : Sec 𝒰 M 0 W) (hc : dSec c = 0) :
    aug0 (cr c (single k) (le_cechOpen_single k hW)) = c := by
  funext s
  simp only [aug0]
  rw [map_cr]
  by_cases hk : k ∈ Set.range s.1
  · rw [cr_congr c (idx_zero_eq_single hk).symm _ le_rfl, cr_self]
  · have h := cocycle_insIdx k hW c hc s hk
    rw [Fin.sum_univ_one, cr_congr c (face_insIdx_zero s k hk) _
      (((𝒰.inter s).ι.image_preimage_le W).trans (le_cechOpen_single k hW))] at h
    have hm := pos_le s.1 k
    have hsum : pos s.1 k + ((insPos 𝒰 s k).succAbove 0 : ℕ) = 1 := by
      have hpos : ((insPos 𝒰 s k) : ℕ) = pos s.1 k := rfl
      rw [val_succAbove, hpos]
      split_ifs <;> omega
    exact (eq_of_sign_add_eq_one hsum h).symm

end Sections

section Sheaf

variable (M : X.Modules) {𝒰}

lemma exists_mem_U (x : X) : ∃ k, x ∈ 𝒰.U k :=
  TopologicalSpace.Opens.mem_iSup.1
    (show x ∈ ⨆ i, 𝒰.U i by rw [𝒰.iSup_eq_top]; exact TopologicalSpace.Opens.mem_top x)

lemma app_map_apply {N N' : X.Modules} (φ : N ⟶ N') {V W : X.Opens} (h : W ≤ V) (x : Γ(N, V)) :
    φ.app W (N.presheaf.map (homOfLE h).op x) = N'.presheaf.map (homOfLE h).op (φ.app V x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- The components over `W` of a section of the `p`-th Čech term. -/
def toSec {p : ℕ} (W : X.Opens) (x : Γ(cechTerm 𝒰 M p, W)) : Sec 𝒰 M p W := fun s =>
  (biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) s).app W x

lemma toSec_injective {p : ℕ} (W : X.Opens) :
    Function.Injective (toSec (𝒰 := 𝒰) (p := p) M W) := fun _ _ h =>
  biproduct_ext_app _ fun s => congrFun h s

lemma toSec_surjective {p : ℕ} (W : X.Opens) :
    Function.Surjective (toSec (𝒰 := 𝒰) (p := p) M W) := fun b =>
  let ⟨x, hx⟩ := biproduct_exists_app (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) W b
  ⟨x, funext fun s => hx s⟩

lemma toSec_zero {p : ℕ} (W : X.Opens) : toSec (𝒰 := 𝒰) (p := p) M W 0 = 0 := by
  funext s
  simp only [toSec, Pi.zero_apply, map_zero]
  rfl

lemma toSec_cechD {p : ℕ} (W : X.Opens) (x : Γ(cechTerm 𝒰 M p, W)) :
    toSec M W ((cechD 𝒰 M p).app W x) = dSec (toSec M W x) := by
  funext t
  change (cechD 𝒰 M p ≫ biproduct.π (fun s : 𝒰.Idx (p + 1) => sheafOn M (𝒰.inter s)) t).app W x = _
  rw [cechD_π, sum_app_apply]
  simp only [dSec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zsmul_app_apply]
  rfl

lemma toSec_augmentation (W : X.Opens) (m : Γ(M, W)) :
    toSec M W ((augmentation 𝒰 M).app W m) = aug0 m := by
  funext s
  change (augmentation 𝒰 M ≫ biproduct.π (fun s : 𝒰.Idx 0 => sheafOn M (𝒰.inter s)) s).app W m = _
  rw [augmentation_π]
  rfl

/-- The augmentation is a monomorphism: sections agreeing on every `𝒰.U i ⊓ V` agree. -/
theorem mono_augmentation : Mono (augmentation 𝒰 M) := by
  refine mono_of_app_injective _ fun V x y hxy => ?_
  have h := congrArg (toSec M V) hxy
  rw [toSec_augmentation, toSec_augmentation] at h
  have hcover : V ≤ ⨆ i, cechOpen 𝒰 (single i) V := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_mem_U (𝒰 := 𝒰) z
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    have hle : 𝒰.U i ⊓ V ≤ cechOpen 𝒰 (single i) V := by
      rw [cechOpen_eq]
      exact inf_le_inf_right V (le_iInf fun _ => le_rfl)
    exact hle (TopologicalSpace.Opens.mem_inf.2 ⟨hi, hz⟩)
  exact TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i => cechOpen 𝒰 (single i) V) V
    (fun i => homOfLE ((𝒰.inter (single i)).ι.image_preimage_le V)) hcover x y
    fun i => congrFun h (single i)

lemma cechD_locally_exact {n : ℕ} (k : 𝒰.ι) {W : X.Opens} (hW : W ≤ 𝒰.U k)
    (c : Γ(cechTerm 𝒰 M (n + 1), W)) (hc : (cechD 𝒰 M (n + 1)).app W c = 0) :
    ∃ b : Γ(cechTerm 𝒰 M n, W), (cechD 𝒰 M n).app W b = c := by
  have hc' : dSec (toSec M W c) = 0 := by
    rw [← toSec_cechD, hc, toSec_zero]
  obtain ⟨b, hb⟩ := toSec_surjective M W (contr k hW (toSec M W c))
  exact ⟨b, toSec_injective M W (by rw [toSec_cechD, hb, dSec_contr k hW _ hc'])⟩

lemma augmentation_locally_exact (k : 𝒰.ι) {W : X.Opens} (hW : W ≤ 𝒰.U k)
    (c : Γ(cechTerm 𝒰 M 0, W)) (hc : (cechD 𝒰 M 0).app W c = 0) :
    ∃ m : Γ(M, W), (augmentation 𝒰 M).app W m = c := by
  have hc' : dSec (toSec M W c) = 0 := by
    rw [← toSec_cechD, hc, toSec_zero]
  exact ⟨cr (toSec M W c) (single k) (le_cechOpen_single k hW), toSec_injective M W
    (by rw [toSec_augmentation, aug0_cr_single k hW _ hc'])⟩

theorem exact_cechSc (n : ℕ) : (cechSc 𝒰 M n).Exact := by
  refine exact_of_locally _ fun V (c : Γ(cechTerm 𝒰 M (n + 1), V)) hc x hx => ?_
  obtain ⟨k, hk⟩ := exists_mem_U (𝒰 := 𝒰) x
  have hW : V ⊓ 𝒰.U k ≤ V := inf_le_left
  obtain ⟨b, hb⟩ := cechD_locally_exact M k (inf_le_right : V ⊓ 𝒰.U k ≤ 𝒰.U k)
    ((cechTerm 𝒰 M (n + 1)).presheaf.map (homOfLE hW).op c)
    (by rw [app_map_apply, show (cechD 𝒰 M (n + 1)).app V c = 0 from hc, map_zero])
  exact ⟨V ⊓ 𝒰.U k, hW, TopologicalSpace.Opens.mem_inf.2 ⟨hx, hk⟩, b, hb⟩

theorem exact_augSc : (augSc 𝒰 M).Exact := by
  refine exact_of_locally _ fun V (c : Γ(cechTerm 𝒰 M 0, V)) hc x hx => ?_
  obtain ⟨k, hk⟩ := exists_mem_U (𝒰 := 𝒰) x
  have hW : V ⊓ 𝒰.U k ≤ V := inf_le_left
  obtain ⟨b, hb⟩ := augmentation_locally_exact M k (inf_le_right : V ⊓ 𝒰.U k ≤ 𝒰.U k)
    ((cechTerm 𝒰 M 0).presheaf.map (homOfLE hW).op c)
    (by rw [app_map_apply, show (cechD 𝒰 M 0).app V c = 0 from hc, map_zero])
  exact ⟨V ⊓ 𝒰.U k, hW, TopologicalSpace.Opens.mem_inf.2 ⟨hx, hk⟩, b, hb⟩

variable (𝒰) in
/-- The augmentation `M[0] ⟶ cechComplex 𝒰 M` is a quasi-isomorphism. -/
theorem quasiIso_cechAug : QuasiIso (cechAug 𝒰 M) :=
  quasiIso_cechAug_of_exact 𝒰 M (mono_augmentation M) (exact_augSc M) (exact_cechSc M)

end Sheaf

end Langlands.AlgebraicGeometry.Modules.CechResolution
