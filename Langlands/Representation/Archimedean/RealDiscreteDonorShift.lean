import Langlands.Representation.Archimedean.RealDiscreteNestedAssembly
import Mathlib.Data.List.OfFn

/-! # A dominant spherical shift of the nested donor -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealDiscreteDonorShift

open Langlands.LocalFactor.Archimedean
open RealDiscreteNestedAssembly RealDiscreteNestedPresentation RealInducedCharacter

/-- The residue of a signed exponent relative to the common real center. The integer `z`
is twice its real displacement from that center. -/
def residue (z : ℤ) (e : Fin 2) : ℤ := (z - 2 * e.val) % 4

private structure Entry where
  data : RealCharacterData
  offset : ℤ

private def center (c : RealCharacterData) : Entry := ⟨c, 0⟩
private def lower (d : ComplexCharacterData) : Entry := ⟨low d, -(d.weight.natAbs : ℤ)⟩
private def upper (d : ComplexCharacterData) : Entry := ⟨high d, d.weight.natAbs⟩

private def shift (B : ℕ) (x : Entry) : ℕ :=
  2 * (if x.offset < 0 then x.offset.natAbs + 1
    else if 0 < x.offset then 3 * B + (B - x.offset.natAbs)
    else 5 * B * x.data.parity.val) + x.data.parity.val

private def Ordered (B : ℕ) (a b : Entry) : Prop :=
  shift B a ≤ shift B b ∧
  b.offset - 2 * (shift B b : ℤ) ≤ a.offset - 2 * (shift B a : ℤ) ∧
  (residue a.offset a.data.parity = residue b.offset b.data.parity → b.offset ≤ a.offset)

private theorem lower_shift (B : ℕ) {d : ComplexCharacterData} (hd : 0 < d.weight.natAbs) :
    shift B (lower d) = 2 * (d.weight.natAbs + 1) + (lowSign d).val := by
  have h : 0 < (d.weight.natAbs : ℤ) := by exact_mod_cast hd
  have h' : -(d.weight.natAbs : ℤ) < 0 := neg_lt_zero.mpr h
  simp only [shift, lower, h', ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast, low, cb_parity]

private theorem upper_shift (B : ℕ) {d : ComplexCharacterData} (hd : 0 < d.weight.natAbs) :
    shift B (upper d) = 2 * (3 * B + (B - d.weight.natAbs)) + (highSign d).val := by
  have h : 0 < (d.weight.natAbs : ℤ) := by exact_mod_cast hd
  simp only [shift, upper, not_lt.mpr h.le, h, ↓reduceIte, Int.natAbs_natCast, high, ca_parity]

private theorem even_shift (B : ℕ) {c : RealCharacterData} (hc : c.parity = 0) :
    shift B (center c) = 0 := by simp [shift, center, hc]

private theorem odd_shift (B : ℕ) {c : RealCharacterData} (hc : c.parity = 1) :
    shift B (center c) = 10 * B + 1 := by
  simp only [shift, center, lt_self_iff_false, ↓reduceIte, hc, Fin.val_one,
    mul_one, ← Nat.mul_assoc]

private theorem even_residue {c : RealCharacterData} (hc : c.parity = 0) :
    residue (center c).offset (center c).data.parity = 0 := by simp [residue, center, hc]

private theorem odd_residue {c : RealCharacterData} (hc : c.parity = 1) :
    residue (center c).offset (center c).data.parity = 2 := by norm_num [residue, center, hc]

private theorem lower_residue (d : ComplexCharacterData) :
    residue (lower d).offset (lower d).data.parity =
      if d.weight.natAbs % 2 = 0 then 0 else 3 := by
  simp only [residue, lower, low, cb_parity, lowSign]
  split_ifs <;> omega

private theorem upper_residue (d : ComplexCharacterData) :
    residue (upper d).offset (upper d).data.parity =
      if d.weight.natAbs % 2 = 0 then 2 else 1 := by
  simp only [residue, upper, high, ca_parity, highSign]
  split_ifs <;> omega

private theorem ordered_centers (B : ℕ) {a b : RealCharacterData}
    (h : a.parity.val ≤ b.parity.val) (ha : a.parity = 0 ∨ a.parity = 1)
    (hb : b.parity = 0 ∨ b.parity = 1) : Ordered B (center a) (center b) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Ordered, center, shift, ha, hb] at h ⊢
  all_goals omega

private theorem ordered_lowers (B : ℕ) {a b : ComplexCharacterData}
    (ha : 0 < a.weight.natAbs) (hb : 0 < b.weight.natAbs)
    (h : a.weight.natAbs ≤ b.weight.natAbs) : Ordered B (lower a) (lower b) := by
  rw [Ordered, lower_shift B ha, lower_shift B hb]
  simp only [lower]
  have h₁ := (lowSign a).isLt
  have h₂ := (lowSign b).isLt
  by_cases heq : a.weight.natAbs = b.weight.natAbs
  · have hs : (lowSign a).val = (lowSign b).val := by simp [lowSign, heq]
    omega
  · omega

private theorem ordered_uppers (B : ℕ) {a b : ComplexCharacterData}
    (ha : 0 < a.weight.natAbs) (hb : 0 < b.weight.natAbs) (hB : a.weight.natAbs < B)
    (h : b.weight.natAbs ≤ a.weight.natAbs) : Ordered B (upper a) (upper b) := by
  rw [Ordered, upper_shift B ha, upper_shift B hb]
  simp only [upper]
  have h₁ := (highSign a).isLt
  have h₂ := (highSign b).isLt
  by_cases heq : a.weight.natAbs = b.weight.natAbs
  · have hs : (highSign a).val = (highSign b).val := by simp [highSign, heq]
    omega
  · omega

private theorem even_lower (B : ℕ) {a : RealCharacterData} {d : ComplexCharacterData}
    (ha : a.parity = 0) (hd : 0 < d.weight.natAbs) : Ordered B (center a) (lower d) := by
  rw [Ordered, even_shift B ha, lower_shift B hd]
  simp only [center, lower]
  omega

private theorem even_upper (B : ℕ) {a : RealCharacterData} {d : ComplexCharacterData}
    (ha : a.parity = 0) (hd : 0 < d.weight.natAbs) (hB : d.weight.natAbs < B) :
    Ordered B (center a) (upper d) := by
  rw [Ordered, even_shift B ha, upper_shift B hd, even_residue ha, upper_residue]
  simp only [center, upper]
  split_ifs <;> omega

private theorem lower_upper (B : ℕ) {d e : ComplexCharacterData}
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (hBd : d.weight.natAbs < B) (hBe : e.weight.natAbs < B) :
    Ordered B (lower d) (upper e) := by
  rw [Ordered, lower_shift B hd, upper_shift B he, lower_residue, upper_residue]
  simp only [lower, upper]
  have h₁ := (lowSign d).isLt
  have h₂ := (highSign e).isLt
  split_ifs <;> omega

private theorem lower_odd (B : ℕ) {a : RealCharacterData} {d : ComplexCharacterData}
    (ha : a.parity = 1) (hd : 0 < d.weight.natAbs) (hB : d.weight.natAbs < B) :
    Ordered B (lower d) (center a) := by
  rw [Ordered, lower_shift B hd, odd_shift B ha, lower_residue, odd_residue ha]
  simp only [center, lower]
  have h₁ := (lowSign d).isLt
  split_ifs <;> omega

private theorem upper_odd (B : ℕ) {a : RealCharacterData} {d : ComplexCharacterData}
    (ha : a.parity = 1) (hd : 0 < d.weight.natAbs) (hB : d.weight.natAbs < B) :
    Ordered B (upper d) (center a) := by
  rw [Ordered, upper_shift B hd, odd_shift B ha]
  simp only [center, upper]
  have h₁ := (highSign d).isLt
  omega

private def entries (even : List RealCharacterData) (ds : List ComplexCharacterData)
    (odd : List RealCharacterData) : List Entry :=
  even.map center ++ (ds.reverse.map lower ++ (ds.map upper ++ odd.map center))

private theorem entries_ordered {even odd : List RealCharacterData} {ds : List ComplexCharacterData}
    {B : ℕ} (heven : ∀ c ∈ even, c.parity = 0) (hodd : ∀ c ∈ odd, c.parity = 1)
    (hw : ∀ d ∈ ds, 0 < d.weight.natAbs ∧ d.weight.natAbs < B)
    (hds : ds.Pairwise (fun d e => e.weight.natAbs ≤ d.weight.natAbs)) :
    (entries even ds odd).Pairwise (Ordered B) := by
  have he : (even.map center).Pairwise (Ordered B) := by
    rw [List.pairwise_map]
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    exact ordered_centers B (by rw [heven a ha, heven b hb]) (Or.inl (heven a ha))
      (Or.inl (heven b hb))
  have ho : (odd.map center).Pairwise (Ordered B) := by
    rw [List.pairwise_map]
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    exact ordered_centers B (by rw [hodd a ha, hodd b hb]) (Or.inr (hodd a ha))
      (Or.inr (hodd b hb))
  have hl : (ds.reverse.map lower).Pairwise (Ordered B) := by
    rw [List.pairwise_map]
    exact (List.pairwise_reverse.mpr hds).imp_of_mem fun {a b} ha hb hab =>
      ordered_lowers B (hw a (List.mem_reverse.mp ha)).1 (hw b (List.mem_reverse.mp hb)).1 hab
  have hu : (ds.map upper).Pairwise (Ordered B) := by
    rw [List.pairwise_map]
    exact hds.imp_of_mem fun {a b} ha hb hab =>
      ordered_uppers B (hw a ha).1 (hw b hb).1 (hw a ha).2 hab
  simp only [entries, List.pairwise_append, List.mem_append]
  refine ⟨he, ⟨hl, ⟨hu, ho, ?_⟩, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    exact upper_odd B (hodd c hc) (hw d hd).1 (hw d hd).2
  · intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    have hd' := hw d (List.mem_reverse.mp hd)
    rcases hy with hy | hy
    · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hy
      exact lower_upper B hd'.1 (hw e he').1 hd'.2 (hw e he').2
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      exact lower_odd B (hodd c hc) hd'.1 hd'.2
  · intro x hx y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    rcases hy with hy | hy | hy
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
      exact even_lower B (heven c hc) (hw d (List.mem_reverse.mp hd)).1
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
      exact even_upper B (heven c hc) (hw d hd).1 (hw d hd).2
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
      exact ordered_centers B (by rw [heven c hc, hodd d hd]; decide) (Or.inl (heven c hc))
        (Or.inr (hodd d hd))

private theorem entry_exponent {even odd : List RealCharacterData} {ds : List ComplexCharacterData}
    {r : ℝ} (heven : ∀ c ∈ even, c.exponent.re = r) (hodd : ∀ c ∈ odd, c.exponent.re = r)
    (hds : ∀ d ∈ ds, d.exponent.re = r) {x : Entry} (hx : x ∈ entries even ds odd) :
    x.data.exponent.re = r + (x.offset : ℝ) / 2 := by
  simp only [entries, List.mem_append] at hx
  rcases hx with hx | hx | hx | hx
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simpa [center] using heven c hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    simp only [lower, low, cb_exponent, bExp, Complex.sub_re, Complex.div_ofNat_re,
      Complex.natCast_re, hds d (List.mem_reverse.mp hd), Int.cast_neg, Int.cast_natCast]
    ring
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    simp [upper, high, aExp, Complex.div_ofNat_re, hds d hd]
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simpa [center] using hodd c hc

/-- The donor admits increasing shifts with its signs and with antitone shifted real
exponents. The shift depends only on the real displacement and parity. Within each residue
class the real exponents of the donor decrease. -/
theorem exists_donor_shift {n : ℕ} {r : ℝ}
    {even odd : List RealCharacterData} {ds : List ComplexCharacterData}
    (he : ∀ c ∈ even, c.exponent.re = r ∧ c.parity = 0)
    (ho : ∀ c ∈ odd, c.exponent.re = r ∧ c.parity = 1)
    (hd : ∀ d ∈ ds, d.exponent.re = r ∧ 0 < d.weight.natAbs)
    (hsort : ds.Pairwise (fun d e => e.weight.natAbs ≤ d.weight.natAbs))
    (hn : (donorChars even ds odd).length = n) :
    ∃ (c : Fin n → RealCharacterData) (z : Fin n → ℤ) (weights : Fin n → ℕ),
      List.ofFn c = donorChars even ds odd ∧
      (∀ i, (c i).exponent.re = r + (z i : ℝ) / 2) ∧
      (∀ i, (c i).parity.val = weights i % 2) ∧ Monotone weights ∧
      Antitone (fun i => ((c i).exponent - (weights i : ℂ)).re) ∧
      (∀ i j, z i = z j → (c i).parity = (c j).parity → weights i = weights j) ∧
      (∀ i j, i < j → residue (z i) (c i).parity = residue (z j) (c j).parity → z j ≤ z i) := by
  classical
  let B := ds.toFinset.sup (fun d => d.weight.natAbs) + 1
  have hB (d : ComplexCharacterData) (hd' : d ∈ ds) : d.weight.natAbs < B :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun d => d.weight.natAbs) (List.mem_toFinset.mpr hd'))
  let L := entries even ds odd
  have hmap : L.map Entry.data = donorChars even ds odd := by
    simp [L, entries, donorChars, nestedChars, List.map_append, List.map_map, Function.comp_def,
      center, lower, upper, List.append_assoc]
  have hL : L.length = n := by rw [← List.length_map Entry.data, hmap, hn]
  let v (i : Fin n) := L.get (Fin.cast hL.symm i)
  have hv : List.ofFn v = L := (List.ofFn_congr hL L.get).symm.trans (List.ofFn_get L)
  have hreal (i : Fin n) : (v i).data.exponent.re = r + ((v i).offset : ℝ) / 2 :=
    entry_exponent (fun c hc => (he c hc).1) (fun c hc => (ho c hc).1) (fun d hd' => (hd d hd').1)
      (by change v i ∈ L; rw [← hv]; exact List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hpair : ∀ (i j : Fin n), i < j → Ordered B (v i) (v j) := by
    have hL' : L.Pairwise (Ordered B) := entries_ordered
      (fun c hc => (he c hc).2) (fun c hc => (ho c hc).2)
      (fun d hd' => ⟨(hd d hd').2, hB d hd'⟩) hsort
    rw [← hv, List.pairwise_ofFn] at hL'
    exact fun i j hij => hL' hij
  refine ⟨fun i => (v i).data, fun i => (v i).offset, fun i => shift B (v i),
    ?_, hreal, ?_, ?_, ?_, ?_, fun i j hij => (hpair i j hij).2.2⟩
  · rw [List.ofFn_comp' v Entry.data, hv, hmap]
  · intro i
    change (v i).data.parity.val = shift B (v i) % 2
    have h := (v i).data.parity.isLt
    unfold shift
    omega
  · intro i j hij
    rcases hij.lt_or_eq with hij | rfl
    · exact (hpair i j hij).1
    · rfl
  · intro i j hij
    rcases hij.lt_or_eq with hij | rfl
    · have hc : (((v j).offset : ℤ) : ℝ) - 2 * (shift B (v j) : ℝ) ≤
          (((v i).offset : ℤ) : ℝ) - 2 * (shift B (v i) : ℝ) := by
        exact_mod_cast (hpair i j hij).2.1
      simp only [Complex.sub_re, Complex.natCast_re, hreal]
      linarith
    · rfl
  · intro i j hz he'
    simp only [shift, hz, he']

end Langlands.Archimedean.RealDiscreteDonorShift
