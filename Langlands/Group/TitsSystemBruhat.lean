import Langlands.Group.TitsSystem
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Order.Lattice.Nat

/-! # Bruhat decomposition and parabolic subgroups of an abstract Tits system

Consequences of `Langlands.Group.IsTitsSystem`: the Bruhat decomposition, the subgroups
`B ⟨X⟩ B`, the classification of subgroups containing `B`, self-normalization, and the
parabolic double-coset bijection. -/

namespace Langlands.Group

variable {G W : Type*} [Group G] [Group W]

namespace TitsSystem

section Length

/-- The word length of `w` with respect to `S` (`0` if `w` is not a product of elements of `S`). -/
noncomputable def length (S : Set W) (w : W) : ℕ :=
  sInf {q | ∃ l : List W, l.length = q ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = w}

variable {S : Set W}

theorem length_le (l : List W) (hl : ∀ x ∈ l, x ∈ S) : length S l.prod ≤ l.length :=
  Nat.sInf_le ⟨l, rfl, hl, rfl⟩

theorem exists_word_of_mem_closure (hS : ∀ s ∈ S, s * s = 1) {w : W}
    (hw : w ∈ Subgroup.closure S) : ∃ l : List W, (∀ x ∈ l, x ∈ S) ∧ l.prod = w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact ⟨[x], by simpa using hx, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨l', hl', rfl⟩ := hy
    exact ⟨l ++ l', fun z hz => (List.mem_append.1 hz).elim (hl z) (hl' z), by simp⟩
  | inv x _ hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨l.reverse, fun z hz => hl z (List.mem_reverse.1 hz), ?_⟩
    have hmap : l.map (fun x => x⁻¹) = l :=
      (List.map_congr_left fun x hx => inv_eq_of_mul_eq_one_right (hS x (hl x hx))).trans
        (List.map_id l)
    rw [List.prod_inv_reverse, hmap]

variable (hS : ∀ s ∈ S, s * s = 1) (hgen : Subgroup.closure S = ⊤)
include hS hgen

theorem exists_word_length (w : W) :
    ∃ l : List W, l.length = length S w ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = w := by
  obtain ⟨l, hl, hw⟩ := exists_word_of_mem_closure hS (hgen ▸ Subgroup.mem_top w)
  have hne : ({q | ∃ l : List W, l.length = q ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = w} : Set ℕ).Nonempty :=
    ⟨l.length, l, rfl, hl, hw⟩
  exact Nat.sInf_mem hne

theorem eq_one_of_length_eq_zero {w : W} (h : length S w = 0) : w = 1 := by
  obtain ⟨l, hl, -, rfl⟩ := exists_word_length hS hgen w
  rw [h, List.length_eq_zero_iff] at hl
  simp [hl]

theorem length_mul_left_le {s : W} (hs : s ∈ S) (w : W) :
    length S (s * w) ≤ length S w + 1 := by
  obtain ⟨l, hl, hlS, rfl⟩ := exists_word_length hS hgen w
  have := length_le (s :: l) (by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hs
    · exact hlS x hx)
  simpa [hl] using this

theorem length_mul_right_le {s : W} (hs : s ∈ S) (w : W) :
    length S (w * s) ≤ length S w + 1 := by
  obtain ⟨l, hl, hlS, rfl⟩ := exists_word_length hS hgen w
  have := length_le (l ++ [s]) (by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hlS x hx
    · rw [List.mem_singleton.1 hx]; exact hs)
  simpa [hl] using this

theorem exists_length_mul_left {w : W} (hw : w ≠ 1) :
    ∃ s ∈ S, length S (s * w) + 1 = length S w := by
  obtain ⟨l, hl, hlS, rfl⟩ := exists_word_length hS hgen w
  cases l with
  | nil => simp at hw
  | cons s l =>
    have hs : s ∈ S := hlS s (by simp)
    have hprod : s * (s :: l).prod = l.prod := by
      simp [← mul_assoc, hS s hs]
    refine ⟨s, hs, le_antisymm ?_ ?_⟩
    · rw [hprod, ← hl]
      simpa using length_le l (fun x hx => hlS x (by simp [hx]))
    · have := length_mul_left_le hS hgen hs (s * (s :: l).prod)
      rwa [← mul_assoc, hS s hs, one_mul] at this

theorem exists_length_mul_right {w : W} (hw : w ≠ 1) :
    ∃ s ∈ S, length S (w * s) + 1 = length S w := by
  obtain ⟨l, hl, hlS, rfl⟩ := exists_word_length hS hgen w
  rcases List.eq_nil_or_concat l with rfl | ⟨l, s, rfl⟩
  · simp at hw
  · rw [List.concat_eq_append] at hl hlS ⊢
    have hs : s ∈ S := hlS s (by simp)
    have hprod : (l ++ [s]).prod * s = l.prod := by
      simp [mul_assoc, hS s hs]
    refine ⟨s, hs, le_antisymm ?_ ?_⟩
    · rw [hprod, ← hl]
      simpa using length_le l (fun x hx => hlS x (by simp [hx]))
    · have := length_mul_right_le hS hgen hs ((l ++ [s]).prod * s)
      rwa [mul_assoc, hS s hs, mul_one] at this

end Length

section Cells

variable {B N : Subgroup G} {π : N →* W}

theorem mem_cell_of_eq {w : W} {n : N} (hn : π n = w) : (n : G) ∈ cell B π w :=
  ⟨n, hn, 1, B.one_mem, 1, B.one_mem, by simp⟩

theorem mul_mem_cell_left {w : W} {g b : G} (hg : g ∈ cell B π w) (hb : b ∈ B) :
    b * g ∈ cell B π w := by
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨n, hn, b * b₁, B.mul_mem hb hb₁, b₂, hb₂, by simp [mul_assoc]⟩

theorem mul_mem_cell_right {w : W} {g b : G} (hg : g ∈ cell B π w) (hb : b ∈ B) :
    g * b ∈ cell B π w := by
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨n, hn, b₁, hb₁, b₂ * b, B.mul_mem hb₂ hb, by simp [mul_assoc]⟩

theorem inv_mem_cell {w : W} {g : G} (hg : g ∈ cell B π w) : g⁻¹ ∈ cell B π w⁻¹ := by
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨n⁻¹, by simp [hn], b₂⁻¹, B.inv_mem hb₂, b₁⁻¹, B.inv_mem hb₁, by simp [mul_assoc]⟩

/-- Points of `N` over `⟨X⟩` lie in any subgroup with underlying set `B ⟨X⟩ B`. -/
theorem rep_mem_of_coe_eq {X : Set W} {P : Subgroup G}
    (hP : (P : Set G) = standardParabolic B π X) {n : N} (hn : π n ∈ Subgroup.closure X) :
    (n : G) ∈ P := by
  rw [← SetLike.mem_coe, hP]
  exact ⟨π n, hn, mem_cell_of_eq rfl⟩

theorem exists_rep_mem_of_mem_closure {H : Subgroup G} {X : Set W}
    (hX : ∀ s ∈ X, ∃ n : N, π n = s ∧ (n : G) ∈ H) {w : W} (hw : w ∈ Subgroup.closure X) :
    ∃ m : N, π m = w ∧ (m : G) ∈ H := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact hX x hx
  | one => exact ⟨1, map_one π, H.one_mem⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm, hmH⟩ := hx
    obtain ⟨m', hm', hm'H⟩ := hy
    exact ⟨m * m', by simp [hm, hm'], H.mul_mem hmH hm'H⟩
  | inv x _ hx =>
    obtain ⟨m, hm, hmH⟩ := hx
    exact ⟨m⁻¹, by simp [hm], H.inv_mem hmH⟩

end Cells

end TitsSystem

namespace IsTitsSystem

open TitsSystem

variable {B N : Subgroup G} {π : N →* W} {S : Set W} (h : IsTitsSystem B N π S)
include h

theorem mem_iff (n : N) : (n : G) ∈ B ↔ π n = 1 := by
  rw [← MonoidHom.mem_ker, h.ker_eq, Subgroup.mem_subgroupOf]

theorem closure_union : Subgroup.closure ((B : Set G) ∪ (N : Set G)) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, h.sup_eq]

theorem inv_eq {s : W} (hs : s ∈ S) : s⁻¹ = s :=
  inv_eq_of_mul_eq_one_right (h.mul_self s hs)

theorem exists_eq_of_mem_cell {w : W} {g : G} (hg : g ∈ cell B π w) {n : N} (hn : π n = w) :
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂ := by
  obtain ⟨m, hm, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  have hmem : ((n⁻¹ * m : N) : G) ∈ B := (h.mem_iff _).2 (by simp [hm, hn])
  refine ⟨b₁, hb₁, ((n⁻¹ * m : N) : G) * b₂, B.mul_mem hmem hb₂, ?_⟩
  simp [mul_assoc]

theorem mem_cell_one_iff {g : G} : g ∈ cell B π 1 ↔ g ∈ B := by
  constructor
  · rintro ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩
    exact B.mul_mem (B.mul_mem hb₁ ((h.mem_iff n).2 hn)) hb₂
  · intro hg
    exact ⟨1, map_one π, 1, B.one_mem, g, hg, by simp⟩

theorem subset_of_mem {H : Subgroup G} (hB : B ≤ H) {w : W} {n : N} (hn : π n = w)
    (hnH : (n : G) ∈ H) {g : G} (hg : g ∈ cell B π w) : g ∈ H := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h.exists_eq_of_mem_cell hg hn
  exact H.mul_mem (H.mul_mem (hB hb₁) hnH) (hB hb₂)

theorem rep_mem_of_mem_cell {H : Subgroup G} (hB : B ≤ H) {w : W} {g : G}
    (hg : g ∈ cell B π w) (hgH : g ∈ H) {n : N} (hn : π n = w) : (n : G) ∈ H := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h.exists_eq_of_mem_cell hg hn
  have := H.mul_mem (H.mul_mem (H.inv_mem (hB hb₁)) hgH) (H.inv_mem (hB hb₂))
  simpa [mul_assoc] using this

theorem mem_cell_mul {v w : W} {g : G} (hg : g ∈ cell B π (v * w)) :
    ∃ x ∈ cell B π v, ∃ y ∈ cell B π w, g = x * y := by
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  obtain ⟨m, hm⟩ := h.surjective v
  refine ⟨b₁ * m, mul_mem_cell_left (mem_cell_of_eq hm) hb₁,
    ((m⁻¹ * n : N) : G) * b₂, mul_mem_cell_right (mem_cell_of_eq (by simp [hm, hn])) hb₂, ?_⟩
  simp [mul_assoc]

/-- Axiom (T3) on cells: `C(s) C(w) ⊆ C(w) ∪ C(sw)`. -/
theorem mul_mem_cell_simple {s w : W} (hs : s ∈ S) {x y : G} (hx : x ∈ cell B π s)
    (hy : y ∈ cell B π w) : x * y ∈ cell B π w ∪ cell B π (s * w) := by
  obtain ⟨ns, hns, b₁, hb₁, b₂, hb₂, rfl⟩ := hx
  obtain ⟨n, hn, b₃, hb₃, b₄, hb₄, rfl⟩ := hy
  have key := h.mul_mem_cell s hs ns n hns (b₂ * b₃) (B.mul_mem hb₂ hb₃)
  rw [hn] at key
  have heq : b₁ * ↑ns * b₂ * (b₃ * ↑n * b₄) = b₁ * (↑ns * (b₂ * b₃) * ↑n) * b₄ := by
    simp [mul_assoc]
  rw [heq]
  rcases key with key | key
  · exact Or.inl (mul_mem_cell_right (mul_mem_cell_left key hb₁) hb₄)
  · exact Or.inr (mul_mem_cell_right (mul_mem_cell_left key hb₁) hb₄)

/-- The right-handed form `C(w) C(s) ⊆ C(w) ∪ C(ws)`. -/
theorem mul_mem_cell_simple_right {s w : W} (hs : s ∈ S) {x y : G} (hx : x ∈ cell B π w)
    (hy : y ∈ cell B π s) : x * y ∈ cell B π w ∪ cell B π (w * s) := by
  have hy' : y⁻¹ ∈ cell B π s := by simpa [h.inv_eq hs] using inv_mem_cell hy
  have key := h.mul_mem_cell_simple hs hy' (inv_mem_cell hx)
  rw [← mul_inv_rev] at key
  rcases key with key | key
  · exact Or.inl (by simpa using inv_mem_cell key)
  · exact Or.inr (by simpa [h.inv_eq hs] using inv_mem_cell key)

/-- For a representative `n` of `s ∈ S` and `b ∈ B` with `n b n⁻¹ ∉ B`, `n b n⁻¹ ∈ C(s)`. -/
theorem conj_mem_cell {s : W} (hs : s ∈ S) {n : N} (hn : π n = s) {b : G} (hb : b ∈ B)
    (hbn : (n : G) * b * (n : G)⁻¹ ∉ B) : (n : G) * b * (n : G)⁻¹ ∈ cell B π s := by
  have := h.mul_mem_cell s hs n n⁻¹ hn b hb
  rw [map_inv, hn, h.inv_eq hs, h.mul_self s hs] at this
  rcases this with h' | h'
  · simpa using h'
  · exact absurd (by simpa using (h.mem_cell_one_iff).1 h') hbn

/-- Bruhat decomposition, existence: every element lies in some cell. -/
theorem exists_mem_cell (g : G) : ∃ w, g ∈ cell B π w := by
  have key : ∀ l : List W, (∀ s ∈ l, s ∈ S) → ∀ x ∈ cell B π l.prod, ∀ (y : G) (w : W),
      y ∈ cell B π w → ∃ w', x * y ∈ cell B π w' := by
    intro l
    induction l with
    | nil =>
      intro _ x hx y w hy
      exact ⟨w, mul_mem_cell_left hy ((h.mem_cell_one_iff).1 (by simpa using hx))⟩
    | cons s l ih =>
      intro hl x hx y w hy
      rw [List.prod_cons] at hx
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h.mem_cell_mul hx
      obtain ⟨w', hw'⟩ := ih (fun t ht => hl t (by simp [ht])) x₂ hx₂ y w hy
      rw [mul_assoc]
      rcases h.mul_mem_cell_simple (hl s (by simp)) hx₁ hw' with hc | hc
      · exact ⟨_, hc⟩
      · exact ⟨_, hc⟩
  have hg : g ∈ Subgroup.closure ((B : Set G) ∪ (N : Set G)) :=
    h.closure_union ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨1, (h.mem_cell_one_iff).2 hx⟩
    · exact ⟨π ⟨x, hx⟩, mem_cell_of_eq rfl⟩
  | one => exact ⟨1, (h.mem_cell_one_iff).2 B.one_mem⟩
  | mul x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨w, hw⟩ := hy
    obtain ⟨l, hl, hlv⟩ :=
      exists_word_of_mem_closure h.mul_self (h.closure_eq ▸ Subgroup.mem_top v)
    exact key l hl x (hlv ▸ hv) y w hw
  | inv x _ hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨v⁻¹, inv_mem_cell hv⟩

private theorem eq_of_mem_cell_aux (q : ℕ) : ∀ (w w' : W) (g : G), length S w = q →
    length S w ≤ length S w' → g ∈ cell B π w → g ∈ cell B π w' → w = w' := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro w w' g hq hle hw hw'
  by_cases h1 : w = 1
  · subst h1
    rw [h.mem_cell_one_iff] at hw
    obtain ⟨n, rfl, b₁, hb₁, b₂, hb₂, rfl⟩ := hw'
    have hn : (n : G) ∈ B := by
      have := B.mul_mem (B.mul_mem (B.inv_mem hb₁) hw) (B.inv_mem hb₂)
      simpa [mul_assoc] using this
    exact ((h.mem_iff n).1 hn).symm
  · obtain ⟨s, hs, hsw⟩ := exists_length_mul_left h.mul_self h.closure_eq h1
    obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hw
    obtain ⟨ns, hns⟩ := h.surjective s
    have hv : ((ns⁻¹ * n : N) : G) ∈ cell B π (s * w) :=
      mem_cell_of_eq (by simp [hns, hn, h.inv_eq hs])
    have hn' : (n : G) ∈ cell B π w' := by
      have := mul_mem_cell_right (mul_mem_cell_left hw' (B.inv_mem hb₁)) (B.inv_mem hb₂)
      simpa [mul_assoc] using this
    have hns' : ((ns⁻¹ : N) : G) ∈ cell B π s := mem_cell_of_eq (by simp [hns, h.inv_eq hs])
    have hx := h.mul_mem_cell_simple hs hns' hn'
    rw [← Subgroup.coe_mul] at hx
    rcases hx with hx | hx
    · have := ih (length S (s * w)) (by omega) (s * w) w' _ rfl (by omega) hv hx
      subst this
      omega
    · have hlen : length S (s * w) ≤ length S (s * w') := by
        have := length_mul_left_le h.mul_self h.closure_eq hs (s * w')
        rw [← mul_assoc, h.mul_self s hs, one_mul] at this
        omega
      have := ih _ (by omega) (s * w) (s * w') _ rfl hlen hv hx
      exact mul_left_cancel this

/-- Bruhat decomposition, uniqueness: distinct elements of `W` give disjoint cells. -/
theorem eq_of_mem_cell {w w' : W} {g : G} (hw : g ∈ cell B π w) (hw' : g ∈ cell B π w') :
    w = w' := by
  rcases le_total (length S w) (length S w') with hle | hle
  · exact h.eq_of_mem_cell_aux _ w w' g rfl hle hw hw'
  · exact (h.eq_of_mem_cell_aux _ w' w g rfl hle hw' hw).symm

private theorem mul_mem_cell_of_length_le_aux {s : W} (hs : s ∈ S) (q : ℕ) :
    ∀ w : W, length S w = q → length S w ≤ length S (s * w) →
      ∀ x ∈ cell B π s, ∀ y ∈ cell B π w, x * y ∈ cell B π (s * w) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro w hq hle x hx y hy
  by_cases h1 : w = 1
  · subst h1
    rw [h.mem_cell_one_iff] at hy
    rw [mul_one]
    exact mul_mem_cell_right hx hy
  · obtain ⟨s', hs', hws'⟩ := exists_length_mul_right h.mul_self h.closure_eq h1
    have hw : w = (w * s') * s' := by rw [mul_assoc, h.mul_self s' hs', mul_one]
    have hy₀ := hy
    rw [hw] at hy₀
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := h.mem_cell_mul hy₀
    have hle' : length S (w * s') ≤ length S (s * (w * s')) := by
      have := length_mul_right_le h.mul_self h.closure_eq hs' (s * (w * s'))
      rw [mul_assoc, mul_assoc, h.mul_self s' hs', mul_one] at this
      omega
    have h₁ := ih (length S (w * s')) (by omega) (w * s') rfl hle' x hx y₁ hy₁
    have h₂ := h.mul_mem_cell_simple_right hs' h₁ hy₂
    rw [mul_assoc s (w * s') s', ← hw] at h₂
    rw [← mul_assoc]
    rcases h₂ with h₂ | h₂
    · exfalso
      have hxinv : x⁻¹ ∈ cell B π s := by simpa [h.inv_eq hs] using inv_mem_cell hx
      have h₃ := h.mul_mem_cell_simple hs hxinv h₂
      have hy' : x⁻¹ * (x * y₁ * y₂) = y₁ * y₂ := by simp [mul_assoc]
      rw [hy', ← mul_assoc s s (w * s'), h.mul_self s hs, one_mul] at h₃
      rcases h₃ with h₃ | h₃
      · have hsw := h.eq_of_mem_cell hy h₃
        have : s * w = w * s' :=
          (congrArg (s * ·) hsw).trans (by rw [← mul_assoc, h.mul_self s hs, one_mul])
        rw [this] at hle
        omega
      · have := h.eq_of_mem_cell hy h₃
        rw [← this] at hws'
        omega
    · exact h₂

/-- If `ℓ(w) ≤ ℓ(sw)` then `C(s) C(w) ⊆ C(sw)`. -/
theorem mul_mem_cell_of_length_le {s w : W} (hs : s ∈ S) (hle : length S w ≤ length S (s * w))
    {x y : G} (hx : x ∈ cell B π s) (hy : y ∈ cell B π w) : x * y ∈ cell B π (s * w) :=
  h.mul_mem_cell_of_length_le_aux hs _ w rfl hle x hx y hy

/-- A subgroup `H ⊇ B` containing a point of `C(w)` contains representatives of all letters of
a reduced word of `w` (Bourbaki, *Lie* IV §2.5, Lemma 2). -/
theorem mem_closure_of_mem (H : Subgroup G) (hB : B ≤ H) (w : W) (n : N) (hn : π n = w)
    (hnH : (n : G) ∈ H) :
    w ∈ Subgroup.closure {s | s ∈ S ∧ ∃ m : N, π m = s ∧ (m : G) ∈ H} := by
  induction hq : length S w using Nat.strong_induction_on generalizing w n with
  | _ q ih =>
  by_cases h1 : w = 1
  · rw [h1]; exact Subgroup.one_mem _
  obtain ⟨s, hs, hsw⟩ := exists_length_mul_left h.mul_self h.closure_eq h1
  have hw : w = s * (s * w) := by rw [← mul_assoc, h.mul_self s hs, one_mul]
  have hle : length S (s * w) ≤ length S (s * (s * w)) := by rw [← hw]; omega
  obtain ⟨ns, hns⟩ := h.surjective s
  obtain ⟨b, hb, hbn⟩ := h.conj_not_le s hs ns hns
  obtain ⟨nv, hnv⟩ := h.surjective (s * w)
  have hcellH : ∀ g ∈ cell B π w, g ∈ H := fun g hg => h.subset_of_mem hB hn hnH hg
  have hx : (ns : G) * b * nv ∈ cell B π w := by
    rw [hw]
    exact h.mul_mem_cell_of_length_le hs hle (mul_mem_cell_right (mem_cell_of_eq hns) hb)
      (mem_cell_of_eq hnv)
  have hy : (ns : G) * nv ∈ cell B π w := by
    rw [hw]
    exact h.mul_mem_cell_of_length_le hs hle (mem_cell_of_eq hns) (mem_cell_of_eq hnv)
  have hc : (ns : G) * b * (ns : G)⁻¹ ∈ H := by
    have := H.mul_mem (hcellH _ hx) (H.inv_mem (hcellH _ hy))
    simpa [mul_assoc] using this
  have hcs := h.conj_mem_cell hs hns hb hbn
  obtain ⟨m, hm⟩ := h.surjective s
  have hmH : (m : G) ∈ H := h.rep_mem_of_mem_cell hB hcs hc hm
  have hsX : s ∈ {s | s ∈ S ∧ ∃ m : N, π m = s ∧ (m : G) ∈ H} := ⟨hs, m, hm, hmH⟩
  have hv := ih (length S (s * w)) (by omega) (s * w) (m⁻¹ * n)
    (by simp [hm, hn, h.inv_eq hs]) (by simpa using H.mul_mem (H.inv_mem hmH) hnH) rfl
  rw [hw]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure hsX) hv

/-- If every generator in `X` has a representative in `H ⊇ B`, then every representative of
every element of `⟨X⟩` lies in `H`. -/
theorem rep_mem_of_mem_closure {H : Subgroup G} (hB : B ≤ H) {X : Set W}
    (hX : ∀ s ∈ X, ∃ n : N, π n = s ∧ (n : G) ∈ H) {w : W} (hw : w ∈ Subgroup.closure X)
    (n : N) (hn : π n = w) : (n : G) ∈ H := by
  obtain ⟨m, hm, hmH⟩ := exists_rep_mem_of_mem_closure hX hw
  exact h.rep_mem_of_mem_cell hB (mem_cell_of_eq hn) (h.subset_of_mem hB hm hmH
    (mem_cell_of_eq hn)) hn

/-- A subgroup `P ⊇ B` equals `B ⟨X⟩ B` once its points of `N` map into `⟨X⟩` and every element
of `⟨X⟩` has a representative in `P`. -/
theorem coe_eq_standardParabolic {P : Subgroup G} (hB : B ≤ P) {X : Set W}
    (hPX : ∀ n : N, (n : G) ∈ P → π n ∈ Subgroup.closure X)
    (hXP : ∀ v ∈ Subgroup.closure X, ∃ n : N, π n = v ∧ (n : G) ∈ P) :
    (P : Set G) = standardParabolic B π X := by
  ext g
  constructor
  · intro hg
    obtain ⟨w, hw⟩ := h.exists_mem_cell g
    obtain ⟨n, hn⟩ := h.surjective w
    exact ⟨w, hn ▸ hPX n (h.rep_mem_of_mem_cell hB hw hg hn), hw⟩
  · rintro ⟨w, hwX, hw⟩
    obtain ⟨n, hn, hnP⟩ := hXP w hwX
    exact h.subset_of_mem hB hn hnP hw

/-- Every subgroup containing `B` is `B ⟨X⟩ B` for some `X ⊆ S`
(Bourbaki, *Lie* IV §2.5, Theorem 3). -/
theorem exists_eq_standardParabolic (H : Subgroup G) (hB : B ≤ H) :
    ∃ X ⊆ S, (H : Set G) = standardParabolic B π X := by
  refine ⟨{s | s ∈ S ∧ ∃ m : N, π m = s ∧ (m : G) ∈ H}, fun s hs => hs.1, ?_⟩
  refine h.coe_eq_standardParabolic hB (fun n hn => h.mem_closure_of_mem H hB _ n rfl hn) ?_
  intro v hv
  obtain ⟨n, hn⟩ := h.surjective v
  exact ⟨n, hn, h.rep_mem_of_mem_closure hB (fun s hs => hs.2) hv n hn⟩

theorem le_of_coe_eq {X : Set W} {P : Subgroup G} (hP : (P : Set G) = standardParabolic B π X) :
    B ≤ P := fun b hb => by
  rw [← SetLike.mem_coe, hP]
  exact ⟨1, Subgroup.one_mem _, (h.mem_cell_one_iff).2 hb⟩

/-- Left multiplication by `B ⟨X⟩ B` moves `C(v)` into cells `C(uv)` with `u ∈ ⟨X⟩`. -/
theorem exists_mul_mem_cell {X : Set W} (hX : X ⊆ S) {u : W} (hu : u ∈ Subgroup.closure X)
    {x : G} (hx : x ∈ cell B π u) {v : W} {y : G} (hy : y ∈ cell B π v) :
    ∃ u' ∈ Subgroup.closure X, x * y ∈ cell B π (u' * v) := by
  obtain ⟨l, hl, rfl⟩ := exists_word_of_mem_closure (fun s hs => h.mul_self s (hX hs)) hu
  clear hu
  induction l generalizing x y v with
  | nil =>
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [one_mul]
    exact mul_mem_cell_left hy ((h.mem_cell_one_iff).1 (by simpa using hx))
  | cons s l ih =>
    rw [List.prod_cons] at hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h.mem_cell_mul hx
    obtain ⟨u', hu', hc⟩ := ih hy (fun t ht => hl t (by simp [ht])) hx₂
    have hs : s ∈ X := hl s (by simp)
    rw [mul_assoc]
    rcases h.mul_mem_cell_simple (hX hs) hx₁ hc with hc' | hc'
    · exact ⟨u', hu', hc'⟩
    · exact ⟨s * u', Subgroup.mul_mem _ (Subgroup.subset_closure hs) hu', by
        rwa [mul_assoc]⟩

theorem exists_mul_mem_cell_right {Y : Set W} (hY : Y ⊆ S) {u : W} (hu : u ∈ Subgroup.closure Y)
    {y : G} (hy : y ∈ cell B π u) {v : W} {x : G} (hx : x ∈ cell B π v) :
    ∃ u' ∈ Subgroup.closure Y, x * y ∈ cell B π (v * u') := by
  obtain ⟨u', hu', hc⟩ :=
    h.exists_mul_mem_cell hY (Subgroup.inv_mem _ hu) (inv_mem_cell hy) (inv_mem_cell hx)
  refine ⟨u'⁻¹, Subgroup.inv_mem _ hu', ?_⟩
  rw [← mul_inv_rev] at hc
  simpa using inv_mem_cell hc

/-- `B ⟨X⟩ B` is a subgroup for `X ⊆ S`. -/
def standardParabolicSubgroup {X : Set W} (hX : X ⊆ S) : Subgroup G where
  carrier := standardParabolic B π X
  mul_mem' := by
    rintro x y ⟨u, hu, hx⟩ ⟨v, hv, hy⟩
    obtain ⟨u', hu', hc⟩ := h.exists_mul_mem_cell hX hu hx hy
    exact ⟨u' * v, Subgroup.mul_mem _ hu' hv, hc⟩
  one_mem' := ⟨1, Subgroup.one_mem _, (h.mem_cell_one_iff).2 B.one_mem⟩
  inv_mem' := by
    rintro x ⟨u, hu, hx⟩
    exact ⟨u⁻¹, Subgroup.inv_mem _ hu, inv_mem_cell hx⟩

theorem coe_standardParabolicSubgroup {X : Set W} (hX : X ⊆ S) :
    (h.standardParabolicSubgroup hX : Set G) = standardParabolic B π X :=
  rfl

/-- Subgroups containing `B` are self-normalizing (Bourbaki, *Lie* IV §2.6, Theorem 4). -/
theorem normalizer_eq_of_le {P : Subgroup G} (hBP : B ≤ P) :
    Subgroup.normalizer (P : Set G) = P := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  have hBM : B ≤ Subgroup.normalizer (P : Set G) := hBP.trans Subgroup.le_normalizer
  intro g hg
  obtain ⟨w, hw⟩ := h.exists_mem_cell g
  obtain ⟨n, hn⟩ := h.surjective w
  have hnM := h.rep_mem_of_mem_cell hBM hw hg hn
  have hwY := h.mem_closure_of_mem _ hBM w n hn hnM
  have hY : ∀ s ∈ {s | s ∈ S ∧ ∃ m : N, π m = s ∧ (m : G) ∈ Subgroup.normalizer (P : Set G)},
      ∃ m : N, π m = s ∧ (m : G) ∈ P := by
    rintro s ⟨hs, m, hm, hmM⟩
    obtain ⟨b, hb, hbm⟩ := h.conj_not_le s hs m hm
    have hcP : (m : G) * b * (m : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 hmM b).1 (hBP hb)
    exact ⟨m, hm, h.rep_mem_of_mem_cell hBP (h.conj_mem_cell hs hm hb hbm) hcP hm⟩
  exact h.subset_of_mem hBP hn (h.rep_mem_of_mem_closure hBP hY hwY n hn) hw

/-- Parabolic double cosets: `⟨X⟩ \ W / ⟨Y⟩ ≃ P \ G / Q` for `P = B ⟨X⟩ B`, `Q = B ⟨Y⟩ B`,
sending the class of `π n` to the class of `n` (Bourbaki, *Lie* IV §2.5, Remark;
Borel–Tits 5.20). -/
theorem exists_doubleCoset_equiv {X Y : Set W} (hX : X ⊆ S) (hY : Y ⊆ S) {V V' : Subgroup W}
    (hV : V = Subgroup.closure X) (hV' : V' = Subgroup.closure Y) {P Q : Subgroup G}
    (hP : (P : Set G) = standardParabolic B π X) (hQ : (Q : Set G) = standardParabolic B π Y) :
    ∃ e : DoubleCoset.Quotient (V : Set W) (V' : Set W) ≃
        DoubleCoset.Quotient (P : Set G) (Q : Set G),
      ∀ n : N, e (DoubleCoset.mk V V' (π n)) = DoubleCoset.mk P Q (n : G) := by
  subst hV hV'
  have hBP := h.le_of_coe_eq hP
  have hBQ := h.le_of_coe_eq hQ
  let rep : W → N := Function.surjInv h.surjective
  have hrep : ∀ w, π (rep w) = w := Function.surjInv_eq h.surjective
  have hmk : ∀ n : N, DoubleCoset.mk P Q ((rep (π n) : N) : G) = DoubleCoset.mk P Q (n : G) := by
    intro n
    rw [DoubleCoset.eq]
    obtain ⟨b₁, hb₁, b₂, hb₂, hn⟩ :=
      h.exists_eq_of_mem_cell (mem_cell_of_eq (rfl : π n = π n)) (hrep (π n))
    exact ⟨b₁, hBP hb₁, b₂, hBQ hb₂, hn⟩
  let f : DoubleCoset.Quotient (Subgroup.closure X : Set W) (Subgroup.closure Y : Set W) →
      DoubleCoset.Quotient (P : Set G) (Q : Set G) :=
    Quotient.lift (fun w => DoubleCoset.mk P Q ((rep w : N) : G)) (by
      intro a b hab
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.rel_iff.1 hab
      have h1 : DoubleCoset.mk P Q ((rep (x * a * y) : N) : G) =
          DoubleCoset.mk P Q (((rep x * rep a * rep y : N) : N) : G) := by
        rw [← hmk (rep x * rep a * rep y)]
        simp [hrep]
      show DoubleCoset.mk P Q ((rep a : N) : G) = DoubleCoset.mk P Q ((rep (x * a * y) : N) : G)
      rw [h1, DoubleCoset.eq]
      refine ⟨rep x, rep_mem_of_coe_eq hP (by rw [hrep]; exact hx),
        rep y, rep_mem_of_coe_eq hQ (by rw [hrep]; exact hy), ?_⟩
      simp)
  have hf : ∀ n : N, f (DoubleCoset.mk _ _ (π n)) = DoubleCoset.mk P Q (n : G) := fun n => hmk n
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
    change DoubleCoset.mk P Q ((rep a : N) : G) = DoubleCoset.mk P Q ((rep b : N) : G) at hab
    rw [DoubleCoset.eq] at hab
    obtain ⟨p, hp, q, hq, hpq⟩ := hab
    rw [← SetLike.mem_coe, hP] at hp
    rw [← SetLike.mem_coe, hQ] at hq
    obtain ⟨u, hu, hpu⟩ := hp
    obtain ⟨u', hu', hqu⟩ := hq
    obtain ⟨u₁, hu₁, h₁⟩ := h.exists_mul_mem_cell hX hu hpu (mem_cell_of_eq (hrep a))
    obtain ⟨u₂, hu₂, h₂⟩ := h.exists_mul_mem_cell_right hY hu' hqu h₁
    rw [← hpq] at h₂
    have := h.eq_of_mem_cell (mem_cell_of_eq (hrep b)) h₂
    apply Quotient.sound
    exact DoubleCoset.rel_iff.2 ⟨u₁, hu₁, u₂, hu₂, this⟩
  · intro z
    induction z using Quotient.inductionOn with
    | h g =>
    obtain ⟨w, hw⟩ := h.exists_mem_cell g
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h.exists_eq_of_mem_cell hw (hrep w)
    refine ⟨DoubleCoset.mk _ _ w, ?_⟩
    change DoubleCoset.mk P Q ((rep w : N) : G) = DoubleCoset.mk P Q (b₁ * (rep w : G) * b₂)
    rw [DoubleCoset.eq]
    exact ⟨b₁, hBP hb₁, b₂, hBQ hb₂, rfl⟩

end IsTitsSystem

end Langlands.Group
