import Langlands.Group.TitsSystemBruhat

/-! # Conjugacy rigidity of standard parabolics in a Tits system -/

namespace Langlands.Group

variable {G W : Type*} [Group G] [Group W]

namespace IsTitsSystem

open TitsSystem

variable {B N : Subgroup G} {π : N →* W} {S : Set W}
  (h : IsTitsSystem B N π S)
include h

/-- An element of `N` conjugating `B` into an overgroup `P` of `B` lies in `P`. -/
theorem rep_mem_of_conjugate_le {P : Subgroup G} (hBP : B ≤ P)
    (n : N) (hconj : ∀ b ∈ B, (n : G)⁻¹ * b * n ∈ P) : (n : G) ∈ P := by
  generalize hn : π n = w
  induction hq : length S w using Nat.strong_induction_on generalizing w n with
  | _ q ih =>
  by_cases h1 : w = 1
  · exact hBP ((h.mem_iff n).2 (hn.trans h1))
  obtain ⟨s, hs, hsw⟩ := exists_length_mul_left h.mul_self h.closure_eq h1
  obtain ⟨ns, hns⟩ := h.surjective s
  obtain ⟨nv, hnv⟩ := h.surjective (s * w)
  have hw : w = s * (s * w) := by rw [← mul_assoc, h.mul_self s hs, one_mul]
  have hle : length S (s * w) ≤ length S (s * (s * w)) := by
    rw [← hw]
    omega
  let Q : Subgroup G := P.comap (MulAut.conj (n : G)⁻¹).toMonoidHom
  have mem_Q (x : G) : x ∈ Q ↔ (n : G)⁻¹ * x * n ∈ P := by
    simp [Q]
  have hBQ : B ≤ Q := fun b hb => (mem_Q b).2 (hconj b hb)
  have hcell : ∀ x ∈ cell B π w, (n : G)⁻¹ * x ∈ P := by
    intro x hx
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h.exists_eq_of_mem_cell hx hn
    simpa [mul_assoc] using P.mul_mem (hconj b₁ hb₁) (hBP hb₂)
  obtain ⟨b, hb, hbn⟩ := h.conj_not_le s hs ns hns
  have hx : (ns : G) * b * nv ∈ cell B π w := by
    rw [hw]
    exact h.mul_mem_cell_of_length_le hs hle
      (mul_mem_cell_right (mem_cell_of_eq hns) hb) (mem_cell_of_eq hnv)
  have hy : (ns : G) * nv ∈ cell B π w := by
    rw [hw]
    exact h.mul_mem_cell_of_length_le hs hle (mem_cell_of_eq hns) (mem_cell_of_eq hnv)
  have hcQ : (ns : G) * b * (ns : G)⁻¹ ∈ Q := by
    apply (mem_Q _).2
    simpa [mul_assoc] using P.mul_mem (hcell _ hx) (P.inv_mem (hcell _ hy))
  have hnsQ : (ns : G) ∈ Q :=
    h.rep_mem_of_mem_cell hBQ (h.conj_mem_cell hs hns hb hbn) hcQ hns
  have hp : (n : G)⁻¹ * ns * n ∈ P := (mem_Q _).1 hnsQ
  have hconj' : ∀ b ∈ B,
      (((ns⁻¹ * n : N) : G))⁻¹ * b * ((ns⁻¹ * n : N) : G) ∈ P := by
    intro b hb
    simpa [mul_assoc] using
      P.mul_mem (P.mul_mem hp (hconj b hb)) (P.inv_mem hp)
  have hn'P : ((ns⁻¹ * n : N) : G) ∈ P :=
    ih (length S (s * w)) (by omega) (ns⁻¹ * n) hconj' (s * w)
      (by simp [hns, hn, h.inv_eq hs]) rfl
  simpa [mul_assoc] using P.mul_mem hn'P hp

/-- Any element conjugating `B` into an overgroup `P` of `B` belongs to `P`. -/
theorem mem_of_conjugate_le {P : Subgroup G} (hBP : B ≤ P)
    (g : G) (hconj : ∀ b ∈ B, g⁻¹ * b * g ∈ P) : g ∈ P := by
  obtain ⟨w, hw⟩ := h.exists_mem_cell g
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := hw
  have hnP : (n : G) ∈ P := h.rep_mem_of_conjugate_le hBP n (by
    intro b hb
    have hc := hconj (b₁ * b * b₁⁻¹) (B.mul_mem (B.mul_mem hb₁ hb) (B.inv_mem hb₁))
    simpa [mul_assoc] using
      P.mul_mem (P.mul_mem (hBP hb₂) hc) (P.inv_mem (hBP hb₂)))
  exact P.mul_mem (P.mul_mem (hBP hb₁) hnP) (hBP hb₂)

/-- The elements transporting `B` into an overgroup `P` are precisely the actual
elements of `P`; the equivalence preserves their underlying elements of `G`. -/
def parabolicTransporterEquiv {P : Subgroup G} (hBP : B ≤ P) :
    {g : G // ∀ b ∈ B, g⁻¹ * b * g ∈ P} ≃ P where
  toFun g := ⟨g.1, h.mem_of_conjugate_le hBP g.1 g.2⟩
  invFun g := ⟨g.1, fun _ hb =>
    P.mul_mem (P.mul_mem (P.inv_mem g.2) (hBP hb)) g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Two conjugate subgroups containing the fixed `B` coincide. -/
theorem eq_of_conjugate_of_le {P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ≤ Q)
    (g : G) (hconj : Q = P.comap (MulAut.conj g⁻¹).toMonoidHom) : P = Q := by
  have hg : g ∈ P := h.mem_of_conjugate_le hBP g (by
    intro b hb
    have := hBQ hb
    simpa [hconj] using this)
  rw [hconj]
  ext x
  change x ∈ P ↔ (MulAut.conj g⁻¹) x ∈ P
  constructor
  · intro hx
    simpa using P.mul_mem (P.mul_mem (P.inv_mem hg) hx) hg
  · intro hx
    have hx' : g⁻¹ * x * g ∈ P := by simpa using hx
    simpa [mul_assoc] using
      P.mul_mem (P.mul_mem hg hx') (P.inv_mem hg)

end IsTitsSystem

end Langlands.Group
