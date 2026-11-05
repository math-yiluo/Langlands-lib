import Langlands.Topology.CompactNormCharacter
import Mathlib.GroupTheory.GroupAction.Defs

/-! # Continuous positive cocycles and compact overgroups -/

noncomputable section

universe u v

open scoped NNReal

namespace Langlands.Topology

variable (H : Type u) [Group H] [TopologicalSpace H]
  (X : Type v) [MulAction H X]

/-- A continuous positive multiplicative cocycle on an action. Only continuity
in the group variable is required; no topology on the acted-on set is used. -/
structure PositiveCocycle where
  value : H → X → ℝ≥0ˣ
  one_value : ∀ x, value 1 x = 1
  mul_value : ∀ g h x, value (g * h) x = value g (h • x) * value h x
  continuous_value : ∀ x, Continuous (fun g => value g x)

namespace PositiveCocycle

variable {H X} (c : PositiveCocycle H X)

/-- The subgroup preserving the positive cocycle at every point. -/
def preservingSubgroup : Subgroup H where
  carrier := {g | ∀ x, c.value g x = 1}
  one_mem' := c.one_value
  mul_mem' {g h} hg hh x := by
    rw [c.mul_value, hg, hh, one_mul]
  inv_mem' {g} hg x := by
    have h := c.mul_value g g⁻¹ x
    simpa only [mul_inv_cancel, c.one_value, hg (g⁻¹ • x), one_mul] using h.symm

@[simp] theorem mem_preservingSubgroup (g : H) :
    g ∈ c.preservingSubgroup ↔ ∀ x, c.value g x = 1 := Iff.rfl

/-- On a fixed point, the cocycle of an element in a compact subgroup is one. -/
theorem value_eq_one_of_mem_compact_of_fixed
    (L : Subgroup H) (hL : IsCompact (L : Set H))
    (x : X) {g : H} (hg : g ∈ L) (hfix : g • x = x) :
    c.value g x = 1 := by
  let f : H → ℝ := fun h => ((c.value h x : ℝ≥0) : ℝ)
  have hf : Continuous f :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (c.continuous_value x))
  obtain ⟨M, hM⟩ := (hL.image hf).bddAbove
  have hpow (h : H) (hh : h • x = x) (n : ℕ) : f (h ^ n) = f h ^ n := by
    induction n with
    | zero => simp [f, c.one_value]
    | succ n hn =>
      rw [pow_succ, pow_succ]
      change ((c.value (h ^ n * h) x : ℝ≥0) : ℝ) = _
      rw [c.mul_value, hh]
      simpa only [Units.val_mul, NNReal.coe_mul, f] using
        congrArg (fun t : ℝ => t * f h) hn
  have hbig : ∀ h ∈ L, h • x = x → ¬ 1 < f h := by
    intro h hh hhx hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
    have hbound := hM ⟨h ^ n, L.pow_mem hh n, rfl⟩
    rw [hpow h hhx n] at hbound
    exact hn.not_ge hbound
  have hpos : 0 < f g := by
    simp only [f, NNReal.coe_pos]
    exact pos_iff_ne_zero.mpr (c.value g x).ne_zero
  have hinvfix : g⁻¹ • x = x := by
    calc
      g⁻¹ • x = g⁻¹ • (g • x) := congrArg (g⁻¹ • ·) hfix.symm
      _ = x := inv_smul_smul g x
  have hinvvalue : c.value g⁻¹ x = (c.value g x)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    have h := c.mul_value g⁻¹ g x
    simpa only [inv_mul_cancel, c.one_value, hfix] using h.symm
  have hinv : f g⁻¹ = (f g)⁻¹ := by
    simp only [f, hinvvalue, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have h1 : ¬ 1 < f g := hbig g hg hfix
  have h2 : ¬ 1 < f g⁻¹ := hbig g⁻¹ (L.inv_mem hg) hinvfix
  rw [hinv, one_lt_inv₀ hpos] at h2
  have hfg : f g = 1 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  apply Units.ext
  apply NNReal.eq
  exact hfg

/-- If a subgroup preserves a positive cocycle and acts transitively, then every
compact overgroup also preserves that cocycle. -/
theorem compactOvergroup_le_preservingSubgroup
    (K : Subgroup H) (hK : K ≤ c.preservingSubgroup)
    (htrans : ∀ x y : X, ∃ k ∈ K, k • x = y)
    (L : Subgroup H) (hL : IsCompact (L : Set H)) (hKL : K ≤ L) :
    L ≤ c.preservingSubgroup := by
  intro g hg x
  obtain ⟨k, hk, hkx⟩ := htrans x (g • x)
  let s : H := k⁻¹ * g
  have hs : s ∈ L := L.mul_mem (L.inv_mem (hKL hk)) hg
  have hsfix : s • x = x := by
    dsimp only [s]
    rw [mul_smul, ← hkx, inv_smul_smul]
  have hsvalue : c.value s x = 1 :=
    c.value_eq_one_of_mem_compact_of_fixed L hL x hs hsfix
  have hks : k * s = g := by simp [s]
  have h := c.mul_value k s x
  rw [hks, hsfix, hK hk x, hsvalue, one_mul] at h
  exact h

end PositiveCocycle
end Langlands.Topology
