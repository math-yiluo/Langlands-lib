import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic.Group

/-! # Twisted saturation of a contracting double coset -/

open Filter Topology

namespace Langlands.Jacquet

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A neighborhood filtration with Iwahori factorizations and one-step contraction in
the two opposite directions. The levels are normal in the initial subgroup. -/
structure StrictIwahoriFiltration (I N M Nbar : Subgroup G) (t : G) (σ : G ≃* G) where
  level : ℕ → Subgroup G
  level_zero : level 0 = I
  level_le : ∀ j, level j ≤ I
  normalizes : ∀ j, I ≤ Subgroup.normalizer (level j : Set G)
  stable : ∀ j x, σ x ∈ level j ↔ x ∈ level j
  cofinal : ∀ U ∈ 𝓝 (1 : G), ∃ j, (level j : Set G) ⊆ U
  factor : ∀ j x, x ∈ level j →
    ∃ l ∈ level j ⊓ Nbar, ∃ m ∈ level j ⊓ M, ∃ a ∈ level j ⊓ N, x = l * m * a
  upper : ∀ j a, a ∈ level j ⊓ N → t * a * t⁻¹ ∈ level (j + 1)
  lower : ∀ j l, l ∈ level j ⊓ Nbar → t⁻¹ * σ.symm l * t ∈ level (j + 1)

namespace StrictIwahoriFiltration

variable {I N M Nbar : Subgroup G} {t : G} {σ : G ≃* G}

theorem stable_initial (h : StrictIwahoriFiltration I N M Nbar t σ) (x : G) :
    σ x ∈ I ↔ x ∈ I := by
  simpa only [h.level_zero] using h.stable 0 x

private theorem refine_orbit (h : StrictIwahoriFiltration I N M Nbar t σ)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (j : ℕ)
    {m w : G} (hm : m ∈ I ⊓ M) (hw : w ∈ h.level j) :
    ∃ i ∈ I, ∃ b ∈ I ⊓ M, ∃ v ∈ h.level (j + 1),
      i⁻¹ * (t * m * w) * σ i = t * b * v := by
  obtain ⟨l, hl, c, hc, a, ha, hw'⟩ := h.factor j w⁻¹ ((h.level j).inv_mem hw)
  have hw'' : w = a⁻¹ * c⁻¹ * l⁻¹ := by
    rw [← inv_inv w, hw']
    group
  let b := m * c⁻¹
  have hb : b ∈ I ⊓ M := mul_mem hm ⟨I.inv_mem (h.level_le j hc.1), M.inv_mem hc.2⟩
  let a' := m * a⁻¹ * m⁻¹
  have ha' : a' ∈ h.level j ⊓ N := by
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (h.normalizes j hm.1) a⁻¹).mp
        ((h.level j).inv_mem ha.1)
    · exact (Subgroup.mem_normalizer_iff.mp (hMN hm.2) a⁻¹).mp (N.inv_mem ha.2)
  let a'' := t * a' * t⁻¹
  let l' := σ.symm l⁻¹
  have ha'' : a'' ∈ h.level (j + 1) := h.upper j a' ha'
  have hl' : l' ∈ h.level j := (h.stable j l').mp
    (by simpa only [l', MulEquiv.apply_symm_apply] using (h.level j).inv_mem hl.1)
  have hσa : σ a'' ∈ h.level (j + 1) := (h.stable (j + 1) a'').mpr ha''
  have hl'' : t⁻¹ * l' * t ∈ h.level (j + 1) := h.lower j l⁻¹
    ⟨(h.level j).inv_mem hl.1, Nbar.inv_mem hl.2⟩
  let i := a'' * l'⁻¹
  have hi : i ∈ I := I.mul_mem (h.level_le (j + 1) ha'') (I.inv_mem (h.level_le j hl'))
  let v := (b⁻¹ * (t⁻¹ * l' * t) * b) * (l⁻¹ * σ a'' * l)
  have hv : v ∈ h.level (j + 1) := by
    refine (h.level (j + 1)).mul_mem ?_ ?_
    · simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (h.normalizes (j + 1) (I.inv_mem hb.1))
          (t⁻¹ * l' * t)).mp hl''
    · simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp
          (h.normalizes (j + 1) (I.inv_mem (h.level_le j hl.1))) (σ a'')).mp hσa
  refine ⟨i, hi, b, hb, v, hv, ?_⟩
  have hσl : σ l' = l⁻¹ := σ.apply_symm_apply l⁻¹
  rw [hw'', show σ i = σ a'' * l by simp only [i, map_mul, map_inv, hσl, inv_inv]]
  dsimp only [i, a'', a', b, v]
  group

variable [IsTopologicalGroup G] [T2Space G]

/-- A compact double coset with opposite strict contractions is exactly the twisted
saturation of the translate of its compact Levi intersection. -/
theorem doubleCoset_eq_twistedLeviSaturation
    (h : StrictIwahoriFiltration I N M Nbar t σ)
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hI : IsCompact (I : Set G)) (hM : IsCompact ((I ⊓ M : Subgroup G) : Set G))
    (hσ : Continuous σ) :
    DoubleCoset.doubleCoset t (I : Set G) (I : Set G) =
      {x | ∃ i ∈ I, ∃ m ∈ I ⊓ M, i⁻¹ * t * m * σ i = x} := by
  let S : Set G := {x | ∃ i ∈ I, ∃ m ∈ I ⊓ M, i⁻¹ * t * m * σ i = x}
  have hS : IsClosed S := by
    let f : G × G → G := fun z => z.1⁻¹ * t * z.2 * σ z.1
    have hf : Continuous f :=
      ((continuous_fst.inv.mul continuous_const).mul continuous_snd).mul
        (hσ.comp continuous_fst)
    have he : S = f '' ((I : Set G) ×ˢ ((I ⊓ M : Subgroup G) : Set G)) := by
      ext x
      constructor
      · rintro ⟨i, hi, m, hm, rfl⟩
        exact ⟨(i, m), ⟨hi, hm⟩, rfl⟩
      · rintro ⟨⟨i, m⟩, ⟨hi, hm⟩, rfl⟩
        exact ⟨i, hi, m, hm, rfl⟩
    rw [he]
    exact ((hI.prod hM).image hf).isClosed
  ext x
  change x ∈ DoubleCoset.doubleCoset t (I : Set G) (I : Set G) ↔ x ∈ S
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    let x := a * t * b
    have hx (j : ℕ) : ∃ i ∈ I, ∃ m ∈ I ⊓ M, ∃ w ∈ h.level j,
        i⁻¹ * x * σ i = t * m * w := by
      induction j with
      | zero =>
        refine ⟨a, ha, 1, one_mem _, b * σ a, ?_, ?_⟩
        · rw [h.level_zero]
          exact I.mul_mem hb ((h.stable_initial a).mpr ha)
        · dsimp only [x]
          group
      | succ j ih =>
        obtain ⟨i, hi, m, hm, w, hw, he⟩ := ih
        obtain ⟨k, hk, m', hm', v, hv, he'⟩ := h.refine_orbit hMN j hm hw
        refine ⟨i * k, I.mul_mem hi hk, m', hm', v, hv, ?_⟩
        rw [map_mul, mul_inv_rev, show k⁻¹ * i⁻¹ * x * (σ i * σ k) =
          k⁻¹ * (i⁻¹ * x * σ i) * σ k by group, he, he']
    rw [← hS.closure_eq]
    apply mem_closure_iff_nhds_one.mpr
    intro U hU
    have hcont : Continuous (fun z : G => x * z * x⁻¹) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hpre : (fun z : G => x * z * x⁻¹) ⁻¹' U ∈ 𝓝 (1 : G) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨j, hj⟩ := h.cofinal _ hpre
    obtain ⟨i, hi, m, hm, w, hw, he⟩ := hx j
    let y := i * t * m * (σ i)⁻¹
    have hy : y ∈ S := ⟨i⁻¹, I.inv_mem hi, m, hm,
      by simp only [map_inv, inv_inv, y]⟩
    have hconj : σ i * w⁻¹ * (σ i)⁻¹ ∈ h.level j :=
      (Subgroup.mem_normalizer_iff.mp (h.normalizes j ((h.stable_initial i).mpr hi)) w⁻¹).mp
        ((h.level j).inv_mem hw)
    refine ⟨y, hy, ?_⟩
    have hyx : y / x = x * (σ i * w⁻¹ * (σ i)⁻¹) * x⁻¹ := by
      have hm' : t * m = (i⁻¹ * x * σ i) * w⁻¹ := by rw [he, mul_inv_cancel_right]
      rw [show y = i * (t * m) * (σ i)⁻¹ by simp only [y, mul_assoc], hm', div_eq_mul_inv]
      group
    rw [hyx]
    exact hj hconj
  · rintro ⟨i, hi, m, hm, rfl⟩
    refine ⟨i⁻¹, I.inv_mem hi, m * σ i, I.mul_mem hm.1 ((h.stable_initial i).mpr hi), ?_⟩
    group

end StrictIwahoriFiltration

/-- The twisted contracting double-coset identity for any group with compact initial
and Levi subgroups and a strict Iwahori filtration. -/
def ContractingDoubleCosetStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (I N M Nbar : Subgroup G) (t : G) (σ : G ≃* G),
    StrictIwahoriFiltration I N M Nbar t σ →
    M ≤ Subgroup.normalizer (N : Set G) →
    IsCompact (I : Set G) → IsCompact ((I ⊓ M : Subgroup G) : Set G) → Continuous σ →
    DoubleCoset.doubleCoset t (I : Set G) (I : Set G) =
      {x | ∃ i ∈ I, ∃ m ∈ I ⊓ M, i⁻¹ * t * m * σ i = x}

theorem contractingDoubleCoset : ContractingDoubleCosetStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ h hMN hI hM hσ =>
    h.doubleCoset_eq_twistedLeviSaturation hMN hI hM hσ

end Langlands.Jacquet
