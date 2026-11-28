import Langlands.BushnellKutzko.DiagonalSplitTypeRefinement

/-! # A deeper lower corner in a filtration subgroup -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The elements of a subgroup `H ⊆ U^m(𝔄)` whose `(2,1)`-block lies in `𝔓^{m+1}`. -/
def lowerBlockSubgroup (L : LatticeChain 𝒪[F] F V) {e₁ e₂ : A} (hadd : e₁ + e₂ = 1)
    (he₁0 : e₁ ∈ L.endFiltration 0) (he₂0 : e₂ ∈ L.endFiltration 0) (H : Subgroup G) (m : ℕ)
    (hm : 1 ≤ m) (hH : H ≤ L.unitFiltration m) : Subgroup G where
  carrier := {g | g ∈ H ∧ e₂ * ((g : A) - 1) * e₁ ∈ L.endFiltration ((m + 1 : ℕ) : ℤ)}
  one_mem' := ⟨H.one_mem, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg21⟩ ⟨hh, hh21⟩
    refine ⟨H.mul_mem hg hh, ?_⟩
    set x := (g : A) - 1 with hx
    set y := (h : A) - 1 with hy
    have hxP : x ∈ L.endFiltration (m : ℤ) := (hH hg).2.2
    have hyP : y ∈ L.endFiltration (m : ℤ) := (hH hh).2.2
    have hexp : e₂ * (((g * h : G) : A) - 1) * e₁ = e₂ * x * e₁ + e₂ * y * e₁ +
        (e₂ * x * e₁) * (y * e₁) + (e₂ * x) * (e₂ * y * e₁) := by
      have hgh : ((g * h : G) : A) - 1 = x + y + x * (e₁ + e₂) * y := by
        rw [hadd, mul_one, Units.val_mul, hx, hy]; noncomm_ring
      rw [hgh]; noncomm_ring
    rw [hexp]
    have hm1 : ((m : ℕ) : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    refine add_mem (add_mem (add_mem hg21 hh21) ?_) ?_
    · have := L.mul_mem_endFiltration hg21 (L.mul_mem_endFiltration hyP he₁0)
      exact L.endFiltration_antitone (by push_cast; omega) this
    · have := L.mul_mem_endFiltration (L.mul_mem_endFiltration he₂0 hxP) hh21
      exact L.endFiltration_antitone (by push_cast; omega) this
  inv_mem' := by
    rintro g ⟨hg, hg21⟩
    refine ⟨H.inv_mem hg, ?_⟩
    set x := (g : A) - 1 with hx
    set x' := ((g⁻¹ : G) : A) - 1 with hx'
    have hxP : x ∈ L.endFiltration (m : ℤ) := (hH hg).2.2
    have hx'P : x' ∈ L.endFiltration (m : ℤ) := (hH (H.inv_mem hg)).2.2
    have hrel : x' = -x - x' * x := by
      have h1 : ((g⁻¹ : G) : A) * (g : A) = 1 := Units.inv_mul g
      have h2 : (1 + x') * (1 + x) = 1 := by rw [hx, hx']; simp
      have h3 : x' + x + x' * x = 0 := by
        have : (1 + x') * (1 + x) - 1 = x' + x + x' * x := by noncomm_ring
        rw [h2, sub_self] at this
        exact this.symm
      calc x' = (x' + x + x' * x) - x - x' * x := by abel
        _ = -x - x' * x := by rw [h3]; abel
    have hexp : e₂ * x' * e₁ = -(e₂ * x * e₁) - (e₂ * x' * e₁) * (x * e₁) -
        (e₂ * x') * (e₂ * x * e₁) := by
      conv_lhs => rw [hrel]
      have : x' * x = x' * (e₁ + e₂) * x := by rw [hadd, mul_one]
      rw [this]; noncomm_ring
    rw [hexp]
    refine sub_mem (sub_mem (neg_mem hg21) ?_) ?_
    · have h1 := mul_mul_mem_endFiltration L he₂0 hx'P he₁0 (by ring : (0 : ℤ) + m + 0 = m)
      have := L.mul_mem_endFiltration h1 (L.mul_mem_endFiltration hxP he₁0)
      exact L.endFiltration_antitone (by push_cast; omega) this
    · have := L.mul_mem_endFiltration (L.mul_mem_endFiltration he₂0 hx'P) hg21
      exact L.endFiltration_antitone (by push_cast; omega) this

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_lowerBlockSubgroup (L : LatticeChain 𝒪[F] F V) {e₁ e₂ : A} (hadd : e₁ + e₂ = 1)
    (he₁0 : e₁ ∈ L.endFiltration 0) (he₂0 : e₂ ∈ L.endFiltration 0) (H : Subgroup G) (m : ℕ)
    (hm : 1 ≤ m) (hH : H ≤ L.unitFiltration m) (g : G) :
    g ∈ lowerBlockSubgroup L hadd he₁0 he₂0 H m hm hH ↔
      g ∈ H ∧ e₂ * ((g : A) - 1) * e₁ ∈ L.endFiltration ((m + 1 : ℕ) : ℤ) :=
  Iff.rfl

end Langlands.BushnellKutzko.SplitBlocks
