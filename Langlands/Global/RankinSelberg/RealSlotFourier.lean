import Langlands.Global.RankinSelberg.RealSlotMatrices
import Langlands.Representation.Archimedean.RealInducedTorusCore

/-! # Fourier expansion along the rotations of several disjoint slots -/

noncomputable section

open Langlands.Archimedean
open Langlands.Archimedean.RealInducedBlockBound
open Langlands.Archimedean.RealInducedTorusCore
open Langlands.Archimedean.RealBlockFourierFinite

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

variable {N : ℕ}

/-- The product of the rotations `r_{s.p}(θ (s.p))` over a list of slots. -/
def rotProd : List (Slot N) → (ℕ → ℝ) → Langlands.GeneralLinear N ℝ
  | [], _ => 1
  | s :: rest, θ => blockRotation N s.p (θ s.p) * rotProd rest θ

/-- The product of the characters `e^{i j θ (s.p)}` over a list of slots and modes. -/
def modeProd : List (Slot N) → List ℤ → (ℕ → ℝ) → ℂ
  | s :: rest, j :: J, θ => expMode j (θ s.p) * modeProd rest J θ
  | _, _, _ => 1

theorem rotProd_mem : ∀ (L : List (Slot N)) (θ : ℕ → ℝ),
    rotProd L θ ∈ unitaryCompact ℝ N
  | [], _ => one_mem _
  | s :: rest, θ => mul_mem (blockRotation_mem_unitaryCompact N s.p _) (rotProd_mem rest θ)

/-- Fourier coefficients along a slot disjoint from a list preserve the degree bound
along the list. -/
theorem hasDegree_blockFourierCoefficient {s : Slot N} {rest : List (Slot N)}
    (hsd : ∀ t ∈ rest, s.p + 1 < t.p ∨ t.p + 1 < s.p) {D : ℕ}
    {u : Langlands.GeneralLinear N ℝ → ℂ} (hu : Continuous u) (hdeg : HasDegree rest D u)
    (j : ℤ) : HasDegree rest D (blockFourierCoefficient N s.p j u) := by
  intro t ht j' hj' k hk
  have hcomm := blockFourierCoefficient_comm (N := N) (p := t.p) (p' := s.p)
    (by rcases hsd t ht with h | h <;> [exact Or.inr h; exact Or.inl h]) hu j' j k
  rw [hcomm]
  exact blockFourierCoefficient_eq_zero_of j fun θ =>
    hdeg t ht j' hj' _ (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)

/-- **Fourier expansion along several slots.** For a continuous right `O(N)`-finite function
of degree at most `D` along pairwise disjoint slots and `k ∈ O(N)`,
`u(r(θ) k) = (2π)^{-|L|} Σ_J coeffs_J u (k) e^{i ⟨J, θ⟩}`, where `|L|` is the number of slots. -/
theorem eq_sum_rotProd (D : ℕ) : ∀ (slots : List (Slot N)),
    slots.Pairwise Slot.Disjoint →
    ∀ {u : Langlands.GeneralLinear N ℝ → ℂ}, Continuous u → IsKFin u → HasDegree slots D u →
      ∀ k ∈ unitaryCompact ℝ N, ∀ θ : ℕ → ℝ,
        u (rotProd slots θ * k) =
          (2 * (Real.pi : ℂ))⁻¹ ^ slots.length * ∑ J ∈ modeLists D slots.length,
            coeffs (withModes slots J) u k * modeProd slots J θ
  | [], _, u, _, _, _, k, _, θ => by
    simp [rotProd, coeffs, withModes, modeLists, modeProd]
  | s :: rest, hpw, u, hu, hK, hdeg, k, hk, θ => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hsd' : ∀ t ∈ rest, s.p + 1 < t.p ∨ t.p + 1 < s.p := hsd
    have hk' : rotProd rest θ * k ∈ unitaryCompact ℝ N := mul_mem (rotProd_mem rest θ) hk
    have hdeg' : HasDegree rest D u := fun t ht => hdeg t (List.mem_cons_of_mem _ ht)
    have hfirst : ∀ j : ℤ, (D : ℤ) < |j| → ∀ k' ∈ unitaryCompact ℝ N,
        blockFourierCoefficient N s.p j u k' = 0 := hdeg s List.mem_cons_self
    rw [show rotProd (s :: rest) θ * k = blockRotation N s.p (θ s.p) * (rotProd rest θ * k) from
      by simp only [rotProd, mul_assoc]]
    rw [eq_sum_of_degree s.hp hu hK hfirst hk' (θ s.p)]
    have hIH : ∀ j : ℤ, blockFourierCoefficient N s.p j u (rotProd rest θ * k) =
        (2 * (Real.pi : ℂ))⁻¹ ^ rest.length * ∑ J ∈ modeLists D rest.length,
          coeffs (withModes rest J) (blockFourierCoefficient N s.p j u) k * modeProd rest J θ := by
      intro j
      exact eq_sum_rotProd D rest hrest (continuous_coeffs hu [setMode s j])
        (isKFin_coeffs hu hK [setMode s j]) (hasDegree_blockFourierCoefficient hsd' hu hdeg' j)
        k hk θ
    simp_rw [hIH]
    have hdJ : ∀ J : List ℤ, ∀ t ∈ withModes rest J, s.p + 1 < t.p ∨ t.p + 1 < s.p := by
      intro J t ht
      obtain ⟨t', ht', j', rfl⟩ := mem_withModes ht
      exact hsd' t' ht'
    have hc : ∀ (j : ℤ) (J : List ℤ),
        coeffs (withModes (s :: rest) (j :: J)) u k =
          coeffs (withModes rest J) (blockFourierCoefficient N s.p j u) k := by
      intro j J
      change blockFourierCoefficient N s.p j (coeffs (withModes rest J) u) k = _
      rw [blockFourierCoefficient_coeffs j hu _ (hdJ J)]
    rw [List.length_cons, sum_modeLists_succ, pow_succ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hc]
    simp only [modeProd]
    ring


/-! ## Slot sets as lists of slots -/

namespace SlotSet

variable (S : SlotSet N)

/-- The slot set with one slot removed. -/
def erase (p : ℕ) : SlotSet N where
  starts := S.starts.erase p
  lt q hq := S.lt q (Finset.mem_of_mem_erase hq)
  sep q hq := fun h => S.sep q (Finset.mem_of_mem_erase hq) (Finset.mem_of_mem_erase h)

variable {S}

theorem inSlot_erase_iff {i : Fin N} {q p : ℕ} {o : Fin 2} :
    (S.erase p).InSlot i q o ↔ S.InSlot i q o ∧ q ≠ p := by
  simp only [InSlot, erase, Finset.mem_erase]
  tauto

/-- Splitting off the block of one slot. -/
theorem diag_eq_blockMat_mul (A : ℕ → Matrix (Fin 2) (Fin 2) ℝ) {p : ℕ} (hp : p ∈ S.starts) :
    S.diag A = RealInducedBlockSlice.blockMat (S.lt p hp) (A p 0 0) (A p 0 1) (A p 1 0) (A p 1 1) *
      (S.erase p).diag A := by
  have hlt := S.lt p hp
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : S.InSlot i p 0 ∨ S.InSlot i p 1
  · have hne : first hp ≠ second hp := by
      intro e; have := congrArg Fin.val e; simp [first, second] at this
    have hfirst : ∀ q o, ¬ (S.erase p).InSlot (first hp) q o := by
      intro q o h
      rw [inSlot_erase_iff] at h
      exact h.2 (S.inSlot_unique h.1 (inSlot_first hp)).1
    have hsecond : ∀ q o, ¬ (S.erase p).InSlot (second hp) q o := by
      intro q o h
      rw [inSlot_erase_iff] at h
      exact h.2 (S.inSlot_unique h.1 (inSlot_second hp)).1
    rw [sum_two (first hp) (second hp) hne]
    · rw [diag_row_other _ hfirst, diag_row_other _ hsecond]
      rcases hi with h | h
      · rw [diag_row _ h]
        have hv : i.val = p := by simpa using h.2
        simp only [RealInducedBlockSlice.blockMat, Matrix.of_apply, RealBlockRotation.ia,
          RealBlockRotation.ib, first, second, Fin.ext_iff, hv]
        by_cases h1 : j.val = p
        · simp [h1]
        · by_cases h2 : j.val = p + 1
          · simp [h2]
          · simp [h1, h2]
      · rw [diag_row _ h]
        have hv : i.val = p + 1 := by simpa using h.2
        simp only [RealInducedBlockSlice.blockMat, Matrix.of_apply, RealBlockRotation.ia,
          RealBlockRotation.ib, first, second, Fin.ext_iff, hv]
        by_cases h1 : j.val = p
        · simp [h1]
        · by_cases h2 : j.val = p + 1
          · simp [h2]
          · simp [h1, h2]
    · intro k hk1 hk2
      have h1 : k.val ≠ p := fun e => hk1 (Fin.ext (by simp [first, e]))
      have h2 : k.val ≠ p + 1 := fun e => hk2 (Fin.ext (by simp [second, e]))
      have hiv : i.val = p ∨ i.val = p + 1 := by
        rcases hi with h | h
        · left; simpa using h.2
        · right; simpa using h.2
      have hb : RealInducedBlockSlice.blockMat (S.lt p hp) (A p 0 0) (A p 0 1) (A p 1 0)
          (A p 1 1) i k = 0 := by
        simp only [RealInducedBlockSlice.blockMat, Matrix.of_apply, RealBlockRotation.ia,
          RealBlockRotation.ib, Fin.ext_iff]
        rcases hiv with hv | hv <;> simp [hv, h1, h2]
      rw [hb, zero_mul]
  · push Not at hi
    have hblock : ∀ k, RealInducedBlockSlice.blockMat (S.lt p hp) (A p 0 0) (A p 0 1) (A p 1 0)
        (A p 1 1) i k = if i = k then 1 else 0 := by
      intro k
      have h1 : i.val ≠ p := fun e => hi.1 ⟨hp, by simp [e]⟩
      have h2 : i.val ≠ p + 1 := fun e => hi.2 ⟨hp, by simp [e]⟩
      simp only [RealInducedBlockSlice.blockMat, Matrix.of_apply, RealBlockRotation.ia,
        RealBlockRotation.ib, Fin.ext_iff, h1, h2, ite_false]
    simp_rw [hblock, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_univ _))]
    rcases S.inSlot_or i with ⟨q, o, h⟩ | h
    · have hq : q ≠ p := by
        rintro rfl
        obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
        · exact hi.1 h
        · exact hi.2 h
      rw [diag_row _ h, diag_row _ (inSlot_erase_iff.mpr ⟨h, hq⟩)]
    · have h' : ∀ q o, ¬ (S.erase p).InSlot i q o := fun q o hh =>
        h q o (inSlot_erase_iff.mp hh).1
      rw [diag_row_other _ h, diag_row_other _ h']

theorem rot_eq_blockRotation_mul (θ : ℕ → ℝ) {p : ℕ} (hp : p ∈ S.starts) :
    S.rot θ = blockRotation N p (θ p) * (S.erase p).rot θ := by
  apply Units.ext
  rw [Units.val_mul, rot, rot, diagGL_val, diagGL_val, diag_eq_blockMat_mul _ hp,
    RealInducedBlockSlice.blockRotation_eq_blockMat (S.lt p hp)]
  simp [rot2]

end SlotSet

/-- Slots at the positions of a list, with prescribed weights and the other data zero. -/
def mkSlots : (L : List ℕ) → (∀ p ∈ L, p + 1 < N) → (ℕ → ℕ) → List (Slot N)
  | [], _, _ => []
  | p :: L, h, m => ⟨p, h p List.mem_cons_self, 0, m p, 0, 0, 0, 0⟩ ::
      mkSlots L (fun q hq => h q (List.mem_cons_of_mem _ hq)) m

theorem mem_mkSlots : ∀ {L : List ℕ} {h : ∀ p ∈ L, p + 1 < N} {m : ℕ → ℕ} {t : Slot N},
    t ∈ mkSlots L h m → t.p ∈ L ∧ t.M = m t.p
  | [], _, _, _, ht => by simp [mkSlots] at ht
  | p :: L, h, m, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := mem_mkSlots ht
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem length_mkSlots : ∀ (L : List ℕ) (h : ∀ p ∈ L, p + 1 < N) (m : ℕ → ℕ),
    (mkSlots L h m).length = L.length
  | [], _, _ => rfl
  | _ :: L, h, m => by simp [mkSlots, length_mkSlots L]

theorem rot_eq_rotProd (θ : ℕ → ℝ) (m : ℕ → ℕ) : ∀ (L : List ℕ) (S : SlotSet N),
    S.starts = L.toFinset → L.Nodup → ∀ (h : ∀ p ∈ L, p + 1 < N),
      S.rot θ = rotProd (mkSlots L h m) θ
  | [], S, hS, _, _ => by
    apply Units.ext
    rw [SlotSet.rot, SlotSet.diagGL_val]
    ext i j
    have h : ∀ q o, ¬ S.InSlot i q o := fun q o hh => by
      have := hh.1; rw [hS] at this; simp at this
    rw [SlotSet.diag_row_other _ h]
    change _ = ((1 : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i j
    rw [Units.val_one, Matrix.one_apply]
    simp only [eq_comm]
  | p :: L, S, hS, hnd, h => by
    have hp : p ∈ S.starts := by rw [hS]; simp
    rw [SlotSet.rot_eq_blockRotation_mul θ hp]
    simp only [mkSlots, rotProd]
    congr 1
    apply rot_eq_rotProd θ m L (S.erase p)
    · rw [SlotSet.erase]
      change S.starts.erase p = L.toFinset
      rw [hS, List.toFinset_cons, Finset.erase_insert]
      exact fun hh => (List.nodup_cons.mp hnd).1 (List.mem_toFinset.mp hh)
    · exact (List.nodup_cons.mp hnd).2

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
