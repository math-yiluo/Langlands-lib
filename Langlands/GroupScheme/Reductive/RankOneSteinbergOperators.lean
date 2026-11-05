import Langlands.GroupScheme.SplitExistence.WeylModule
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! # Simplicity of the rank-one divided-power operators at Steinberg exponents -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.RankOneSteinberg

open SplitExistence

section Binomial

variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- Every binomial coefficient in row p^s-1 is an alternating unit in characteristic p. -/
theorem choose_steinberg_cast (s r : ℕ) (hr : r ≤ p ^ s - 1) :
    ((p ^ s - 1).choose r : R) = (-1) ^ r := by
  revert hr
  induction r with
  | zero => intro hr; simp
  | succ r ih =>
    intro hr
    have hp : p.Prime := Fact.out
    have hq : p ^ s - 1 + 1 = p ^ s := Nat.sub_add_cancel (pow_pos hp.pos s)
    have hz : ((p ^ s).choose (r + 1) : R) = 0 := by
      apply (CharP.cast_eq_zero_iff R p _).mpr
      exact hp.dvd_choose_pow (by omega) (by omega)
    have hpascal : ((p ^ s - 1).choose r : R) +
        ((p ^ s - 1).choose (r + 1) : R) = 0 := by
      rw [← Nat.cast_add, ← Nat.choose_succ_succ]
      change ((p ^ s - 1 + 1).choose (r + 1) : R) = 0
      rw [hq]
      exact hz
    rw [pow_succ]
    rw [← ih (by omega)]
    linear_combination hpascal

/-- In particular no coefficient in the Steinberg row vanishes in a nonzero ring. -/
theorem choose_steinberg_cast_ne_zero [Nontrivial R] (s r : ℕ) (hr : r ≤ p ^ s - 1) :
    ((p ^ s - 1).choose r : R) ≠ 0 := by
  rw [choose_steinberg_cast p s r hr]
  simpa using Units.ne_zero ((-1 : Rˣ) ^ r)

end Binomial

section Operators

variable (k : Type u) [Field k] (m : ℕ)

/-- The integral divided raising power, mapped into the coefficient field. -/
def raising (a : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  (gamE m a).map (Int.castRingHom k)

/-- The integral divided lowering power, mapped into the coefficient field. -/
def lowering (a : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  (gamF m a).map (Int.castRingHom k)

/-- Actual subspaces stable under all the specified divided-power matrices. -/
def DividedPowerInvariantSubmodule : Type u :=
  {W : Submodule k (Fin (m + 1) → k) //
    (∀ a (x : Fin (m + 1) → k), x ∈ W → raising k m a *ᵥ x ∈ W) ∧
    (∀ a (x : Fin (m + 1) → k), x ∈ W → lowering k m a *ᵥ x ∈ W)}

/-- A suitable raising power takes a vector with no lower support to the top basis line. -/
theorem raising_to_top (x : Fin (m + 1) → k) (j : Fin (m + 1))
    (hx : ∀ c : Fin (m + 1), c < j → x c = 0) :
    raising k m (m - j) *ᵥ x =
      (((m.choose (m - j) : k) * x j) • Pi.single (Fin.last m) (1 : k)) := by
  ext r
  change (∑ c, raising k m (m - j) r c * x c) = _
  rw [Finset.sum_eq_single j]
  · have hj : (j : ℕ) + (m - j) = m := Nat.add_sub_of_le (Nat.le_of_lt_succ j.isLt)
    by_cases hr : r = Fin.last m
    · subst r
      simp [raising, gamE, hj]
    · have hr' : m ≠ (r : ℕ) := by
        intro h
        exact hr (Fin.ext h.symm)
      simp [raising, gamE, hj, hr', hr]
  · intro c hc hcj
    by_cases hlt : c < j
    · simp [hx c hlt]
    · have hc' : (j : ℕ) < c := by
        have : j < c := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hcj)
        exact this
      have hn : (c : ℕ) + (m - j) ≠ (r : ℕ) := by
        have := r.isLt
        have := j.isLt
        omega
      simp [raising, gamE, hn]
  · simp

/-- Divided lowering powers take the top basis vector to each basis vector with coefficient one. -/
theorem lowering_top (r : Fin (m + 1)) :
    lowering k m (m - r) *ᵥ Pi.single (Fin.last m) (1 : k) = Pi.single r 1 := by
  ext c
  rw [Matrix.mulVec_single]
  by_cases hcr : c = r
  · subst c
    have hr : (r : ℕ) + (m - r) = m := Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)
    simp [lowering, gamF, hr]
  · have hn : (c : ℕ) + (m - r) ≠ m := by
      have := c.isLt
      have := r.isLt
      intro h
      apply hcr
      apply Fin.ext
      omega
    simp [lowering, gamF, hn, hcr]

/-- Nonvanishing of the last binomial row forces divided-power invariant subspaces to be trivial. -/
theorem invariant_eq_bot_or_top
    (hchoose : ∀ r ≤ m, (m.choose r : k) ≠ 0)
    (W : DividedPowerInvariantSubmodule k m) : W.val = ⊥ ∨ W.val = ⊤ := by
  classical
  by_cases hW : W.val = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  let s := Finset.univ.filter (fun c : Fin (m + 1) => x c ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨c, hc⟩ : ∃ c, x c ≠ 0 := Function.ne_iff.mp hx0
    exact ⟨c, by simpa [s] using hc⟩
  let j := s.min' hs
  have hj : x j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hbelow (c : Fin (m + 1)) (hc : c < j) : x c = 0 := by
    by_contra h
    have hmem : c ∈ s := by simpa [s] using h
    exact (not_le_of_gt hc) (Finset.min'_le s c hmem)
  have htop_scaled : (((m.choose (m - j) : k) * x j) •
      Pi.single (Fin.last m) (1 : k)) ∈ W.val := by
    rw [← raising_to_top k m x j hbelow]
    exact W.property.1 _ x hx
  have ha : ((m.choose (m - j) : k) * x j) ≠ 0 :=
    mul_ne_zero (hchoose _ (Nat.sub_le _ _)) hj
  have htop : Pi.single (Fin.last m) (1 : k) ∈ W.val := by
    have h := W.val.smul_mem (((m.choose (m - j) : k) * x j)⁻¹) htop_scaled
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h
  have hbasis (r : Fin (m + 1)) : Pi.single r (1 : k) ∈ W.val := by
    rw [← lowering_top k m r]
    exact W.property.2 _ _ htop
  apply Submodule.eq_top_iff'.mpr
  intro v
  have hv : v = ∑ r, v r • Pi.single r (1 : k) := by
    ext c
    simp [Pi.single_apply]
  rw [hv]
  exact W.val.sum_mem fun r _ => W.val.smul_mem _ (hbasis r)

/-- The rank-one divided-power matrices have no nontrivial invariant subspace at p^s-1. -/
theorem steinberg_invariant_eq_bot_or_top (p : ℕ) [Fact p.Prime] [CharP k p]
    (s : ℕ) (W : DividedPowerInvariantSubmodule k (p ^ s - 1)) :
    W.val = ⊥ ∨ W.val = ⊤ := by
  apply invariant_eq_bot_or_top
  exact fun r hr => choose_steinberg_cast_ne_zero p s r hr

end Operators

end Langlands.GroupScheme.RankOneSteinberg
