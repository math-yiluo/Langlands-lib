import Langlands.Group.TitsSystemBruhat
import Mathlib.Tactic.Group

/-! # The Tits multiplication axiom from a rank-one factorization

Let `B, N ≤ G`, `π : N →* W` and `s ∈ W` with `s * s = 1`. Suppose that every `b ∈ B` is a
product `b' * u` with `b' ∈ B'` and `u ∈ U`, that every representative `n` of `s` conjugates
`B'` into `B` and `U` into `B ∪ B s B`, and that every `w ∈ W` satisfies `w ∈ P` or `s * w ∈ P`,
where the representatives `m` of an element of `P` conjugate `U` into `B` by `u ↦ m⁻¹ * u * m`.
Then `s B w ⊆ B w B ∪ B s w B` for all representatives: this is the field `mul_mem_cell` of
`Langlands.Group.IsTitsSystem` for `s`. This is the group-theoretic part of the proof of
Borel–Tits, *Groupes réductifs*, 5.16 (i), with `B' = Z(S)(k) V_a(k)`, `U = U_(a)(k)` and
`P = {w | w⁻¹(a) > 0}`. -/

namespace Langlands.Group

namespace TitsSystem

variable {G W : Type*} [Group G] [Group W] {B N : Subgroup G} {π : N →* W}

/-- If `B = B' U`, a representative `n` of `s` conjugates `B'` into `B`, and `m⁻¹ U m ⊆ B`, then
`n B m ⊆ B n m B`. -/
theorem mul_mem_cell_of_conj_mem {s : W} {B' U : Set G}
    (hBU : ∀ b ∈ B, ∃ b' ∈ B', ∃ u ∈ U, b = b' * u)
    (hB' : ∀ n : N, π n = s → ∀ b' ∈ B', (n : G) * b' * (n : G)⁻¹ ∈ B)
    {n m : N} (hn : π n = s) (hm : ∀ u ∈ U, (m : G)⁻¹ * u * m ∈ B) {b : G} (hb : b ∈ B) :
    (n : G) * b * m ∈ cell B π (s * π m) := by
  obtain ⟨b', hb', u, hu, rfl⟩ := hBU b hb
  refine ⟨n * m, by rw [map_mul, hn], _, hB' n hn b' hb', _, hm u hu, ?_⟩
  simp only [Subgroup.coe_mul]
  group

/-- **The Tits multiplication axiom from a rank-one factorization.** Let `s * s = 1`. Suppose
`B = B' U`, every representative `n` of `s` conjugates `B'` into `B` and `U` into
`B ∪ B s B`, the representatives of every `w ∈ P` conjugate `U` into `B` (by `u ↦ m⁻¹ u m`),
and for every `w`, `w ∈ P` or `s * w ∈ P`. Then `n b m ∈ B (π m) B ∪ B (s π m) B` for every
representative `n` of `s`, `b ∈ B` and `m ∈ N`. -/
theorem mul_mem_cell_of_rankOne {s : W} (hs : s * s = 1) {B' U : Set G} {P : Set W}
    (hBU : ∀ b ∈ B, ∃ b' ∈ B', ∃ u ∈ U, b = b' * u)
    (hB' : ∀ n : N, π n = s → ∀ b' ∈ B', (n : G) * b' * (n : G)⁻¹ ∈ B)
    (hU : ∀ n : N, π n = s → ∀ u ∈ U, (n : G) * u * (n : G)⁻¹ ∈ (B : Set G) ∪ cell B π s)
    (hP : ∀ w ∈ P, ∀ m : N, π m = w → ∀ u ∈ U, (m : G)⁻¹ * u * m ∈ B)
    (hcover : ∀ w : W, w ∈ P ∨ s * w ∈ P)
    (n m : N) (hn : π n = s) {b : G} (hb : b ∈ B) :
    (n : G) * b * m ∈ cell B π (π m) ∪ cell B π (s * π m) := by
  rcases hcover (π m) with hm | hm
  · exact Or.inr (mul_mem_cell_of_conj_mem hBU hB' hn (hP _ hm m rfl) hb)
  obtain ⟨b', hb', u, hu, rfl⟩ := hBU b hb
  have hnm : π (n * m) = s * π m := by rw [map_mul, hn]
  have key : (n : G) * (b' * u) * m =
      (n : G) * b' * (n : G)⁻¹ * ((n : G) * u * (n : G)⁻¹) * ((n * m : N) : G) := by
    simp only [Subgroup.coe_mul]
    group
  rw [key]
  rcases hU n hn u hu with h1 | ⟨n', hn', c, hc, c', hc', h2⟩
  · exact Or.inr (mul_mem_cell_left (mem_cell_of_eq hnm) (B.mul_mem (hB' n hn b' hb') h1))
  · left
    have h3 := mul_mem_cell_of_conj_mem hBU hB' hn' (hP _ hm (n * m) hnm) hc'
    rw [hnm, ← mul_assoc s s, hs, one_mul] at h3
    rw [h2]
    have h4 := mul_mem_cell_left h3 (B.mul_mem (hB' n hn b' hb') hc)
    convert h4 using 1
    simp only [mul_assoc]

/-- The field `mul_mem_cell` of `Langlands.Group.IsTitsSystem`, from a rank-one factorization
for each `s ∈ S` as in `mul_mem_cell_of_rankOne`. -/
theorem forall_mul_mem_cell_of_rankOne {S : Set W} (hS : ∀ s ∈ S, s * s = 1)
    (h : ∀ s ∈ S, ∃ (B' U : Set G) (P : Set W),
      (∀ b ∈ B, ∃ b' ∈ B', ∃ u ∈ U, b = b' * u) ∧
      (∀ n : N, π n = s → ∀ b' ∈ B', (n : G) * b' * (n : G)⁻¹ ∈ B) ∧
      (∀ n : N, π n = s → ∀ u ∈ U, (n : G) * u * (n : G)⁻¹ ∈ (B : Set G) ∪ cell B π s) ∧
      (∀ w ∈ P, ∀ m : N, π m = w → ∀ u ∈ U, (m : G)⁻¹ * u * m ∈ B) ∧
      ∀ w : W, w ∈ P ∨ s * w ∈ P) :
    ∀ s ∈ S, ∀ n m : N, π n = s → ∀ b ∈ B,
      (n : G) * b * m ∈ cell B π (π m) ∪ cell B π (s * π m) := by
  intro s hs n m hn b hb
  obtain ⟨B', U, P, hBU, hB', hU, hP, hcover⟩ := h s hs
  exact mul_mem_cell_of_rankOne (hS s hs) hBU hB' hU hP hcover n m hn hb

end TitsSystem

end Langlands.Group
