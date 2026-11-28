import Langlands.BushnellKutzko.SimpleCharacterFormalIntertwining

/-! # Conjugation of H groups by square-zero perturbations -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- A unit `1 + w` with `w² = 0` normalizes `H^m` when `w x`, `x w` and `w x w` lie in `𝔥^m`
for all `x ∈ 𝔥^m`. -/
theorem mem_normalizer_simpleHGroup_of_sq_eq_zero (S : Stratum 𝒪[F] F V) (hS0 : S.r = 0)
    (hS : S.IsSimple) (q : S.DefiningSequenceChoice) {m : ℕ} (hm : 1 ≤ m) (g : G) {w : A}
    (hg : (g : A) = 1 + w) (hw : w * w = 0)
    (hmul : ∀ x ∈ simpleHLayer S.chain S.n S.b q.tail m,
      w * x ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
        x * w ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
        w * x * w ∈ simpleHLayer S.chain S.n S.b q.tail m) :
    g ∈ Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail m : Set G) := by
  have hginv : ((g⁻¹ : G) : A) = 1 - w := by
    have h1 : (g : A) * (1 - w) = 1 := by
      rw [hg]
      calc (1 + w) * (1 - w) = 1 - w * w := by noncomm_ring
        _ = 1 := by rw [hw, sub_zero]
    calc ((g⁻¹ : G) : A) = ((g⁻¹ : G) : A) * ((g : A) * (1 - w)) := by rw [h1, mul_one]
      _ = 1 - w := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hginv' : ((g⁻¹⁻¹ : G) : A) = 1 + w := by rw [inv_inv, hg]
  -- conjugation by `1 ± w` preserves `1 + 𝔥^m`
  have key : ∀ (u : G) (s : A), (u : A) = 1 + s → ((u⁻¹ : G) : A) = 1 - s →
      (∀ x ∈ simpleHLayer S.chain S.n S.b q.tail m,
        s * x ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
          x * s ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
          s * x * s ∈ simpleHLayer S.chain S.n S.b q.tail m) →
      ∀ h : G, h ∈ simpleHGroup S.chain S.n S.b q.tail m →
        u * h * u⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail m := by
    intro u s hu hu' hs h hh
    rw [simpleHGroup_mem_iff_of_pos S hS0 hS q hm] at hh ⊢
    set x := (h : A) - 1 with hxdef
    obtain ⟨h1, h2, h3⟩ := hs x hh
    have : ((u * h * u⁻¹ : G) : A) - 1 = x + s * x - x * s - s * x * s := by
      rw [Units.val_mul, Units.val_mul, hu, hu', show (h : A) = 1 + x by rw [hxdef]; abel]
      have hss : s * s = 0 := by
        have := Units.mul_inv u
        rw [hu, hu'] at this
        have h' : (1 + s) * (1 - s) = 1 - s * s := by noncomm_ring
        rw [h'] at this
        exact sub_eq_self.mp this
      calc (1 + s) * (1 + x) * (1 - s) - 1 =
          x + s * x - x * s - s * x * s - s * s := by noncomm_ring
        _ = _ := by rw [hss, sub_zero]
    rw [this]
    exact sub_mem (sub_mem (add_mem hh h1) h2) h3
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g w hg hginv hmul h
  · intro hh
    have hmul' : ∀ x ∈ simpleHLayer S.chain S.n S.b q.tail m,
        -w * x ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
          x * -w ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
          -w * x * -w ∈ simpleHLayer S.chain S.n S.b q.tail m := fun x hx => by
      obtain ⟨h1, h2, h3⟩ := hmul x hx
      refine ⟨by simpa using neg_mem h1, by simpa using neg_mem h2, by simpa using h3⟩
    have h' := key g⁻¹ (-w) (by rw [hginv]; abel) (by rw [hginv']; abel) hmul' _ hh
    have heq : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [heq] at h'

end Langlands.BushnellKutzko.SplitBlocks
