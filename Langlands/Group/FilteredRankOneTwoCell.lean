import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-! # Group algebra for a filtered rank-one two-cell decomposition -/

open scoped Pointwise

namespace Langlands.Group.FilteredRankOne

variable {G : Type*} [Group G]

/-- The reflection cell `U m Z U`, in the original ambient group. -/
def reflectionCell (U Z : Subgroup G) (m : G) : Set G :=
  (U : Set G) * {m} * (Z : Set G) * (U : Set G)

theorem mem_reflectionCell_iff {U Z : Subgroup G} {m g : G} :
    g ∈ reflectionCell U Z m ↔
      ∃ a ∈ U, ∃ z ∈ Z, ∃ b ∈ U, a * m * z * b = g := by
  constructor
  · rintro ⟨_, ⟨_, ⟨a, ha, _, rfl, rfl⟩, z, hz, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, z, hz, b, hb, rfl⟩
  · rintro ⟨a, ha, z, hz, b, hb, rfl⟩
    exact ⟨a * m * z, ⟨a * m, ⟨a, ha, m, rfl, rfl⟩, z, hz, rfl⟩, b, hb, rfl⟩

/-- A subgroup given as `V⁺ Z U` also admits the reverse factor order. -/
theorem exists_reverse_factors {U Vplus Z B : Subgroup G}
    (hB : (B : Set G) = (Vplus : Set G) * (Z : Set G) * (U : Set G))
    {g : G} (hg : g ∈ B) :
    ∃ a ∈ U, ∃ z ∈ Z, ∃ b ∈ Vplus, a * z * b = g := by
  have hgi : g⁻¹ ∈ (Vplus : Set G) * (Z : Set G) * (U : Set G) := by
    rw [← hB]
    exact B.inv_mem hg
  obtain ⟨_, ⟨b, hb, z, hz, rfl⟩, a, ha, heq⟩ := hgi
  refine ⟨a⁻¹, U.inv_mem ha, z⁻¹, Z.inv_mem hz, b⁻¹, Vplus.inv_mem hb, ?_⟩
  have hi := congrArg Inv.inv heq
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi

/-- The purely group-theoretic step in the filtered rank-one decomposition.
All filtration, centralizer and conjugation inputs remain explicit. -/
theorem coe_sup_eq_twoCell {U V Vplus Z B : Subgroup G} {m : G}
    (hplus : Vplus ≤ V)
    (hB : (B : Set G) = (Vplus : Set G) * (Z : Set G) * (U : Set G))
    (hm : m ∈ U ⊔ V ⊔ Z)
    (hsq : m ^ 2 ∈ Z)
    (hZU : ∀ z ∈ Z, ∀ a ∈ U, z * a * z⁻¹ ∈ U)
    (hmZ : ∀ z ∈ Z, m⁻¹ * z * m ∈ Z)
    (hmU : ∀ a ∈ U, m⁻¹ * a * m ∈ V)
    (hmV : ∀ b ∈ V, m⁻¹ * b * m ∈ U)
    (hV : (V : Set G) ⊆ (Vplus : Set G) ∪ reflectionCell U Z m) :
    ((U ⊔ V ⊔ Z : Subgroup G) : Set G) = (B : Set G) ∪ reflectionCell U Z m := by
  have hUB : U ≤ B := by
    intro a ha
    rw [← SetLike.mem_coe, hB]
    exact ⟨1, ⟨1, Vplus.one_mem, 1, Z.one_mem, one_mul 1⟩, a, ha, one_mul a⟩
  have hZB : Z ≤ B := by
    intro z hz
    rw [← SetLike.mem_coe, hB]
    exact ⟨z, ⟨1, Vplus.one_mem, z, hz, one_mul z⟩, 1, U.one_mem, mul_one z⟩
  have hplusB : Vplus ≤ B := by
    intro b hb
    rw [← SetLike.mem_coe, hB]
    exact ⟨b, ⟨b, hb, 1, Z.one_mem, mul_one b⟩, 1, U.one_mem, mul_one b⟩
  have hCrightU : ∀ g ∈ reflectionCell U Z m, ∀ a ∈ U,
      g * a ∈ reflectionCell U Z m := by
    intro g hg a ha
    obtain ⟨b, hb, z, hz, c, hc, rfl⟩ := mem_reflectionCell_iff.mp hg
    apply mem_reflectionCell_iff.mpr
    exact ⟨b, hb, z, hz, c * a, U.mul_mem hc ha, (mul_assoc _ _ _).symm⟩
  have hCrightZ : ∀ g ∈ reflectionCell U Z m, ∀ z ∈ Z,
      g * z ∈ reflectionCell U Z m := by
    intro g hg z hz
    obtain ⟨a, ha, t, ht, b, hb, rfl⟩ := mem_reflectionCell_iff.mp hg
    apply mem_reflectionCell_iff.mpr
    refine ⟨a, ha, t * z, Z.mul_mem ht hz, z⁻¹ * b * z, ?_, ?_⟩
    · simpa only [inv_inv] using hZU z⁻¹ (Z.inv_mem hz) b hb
    · group
  have hCleftUZ : ∀ a ∈ U, ∀ z ∈ Z, ∀ g ∈ reflectionCell U Z m,
      a * z * g ∈ reflectionCell U Z m := by
    intro a ha z hz g hg
    obtain ⟨b, hb, t, ht, c, hc, rfl⟩ := mem_reflectionCell_iff.mp hg
    apply mem_reflectionCell_iff.mpr
    refine ⟨a * (z * b * z⁻¹), U.mul_mem ha (hZU z hz b hb),
      (m⁻¹ * z * m) * t, Z.mul_mem (hmZ z hz) ht, c, hc, ?_⟩
    group
  have hrightU : ∀ g ∈ (B : Set G) ∪ reflectionCell U Z m, ∀ a ∈ U,
      g * a ∈ (B : Set G) ∪ reflectionCell U Z m := by
    intro g hg a ha
    exact hg.elim (fun h => Or.inl (B.mul_mem h (hUB ha)))
      (fun h => Or.inr (hCrightU g h a ha))
  have hrightZ : ∀ g ∈ (B : Set G) ∪ reflectionCell U Z m, ∀ z ∈ Z,
      g * z ∈ (B : Set G) ∪ reflectionCell U Z m := by
    intro g hg z hz
    exact hg.elim (fun h => Or.inl (B.mul_mem h (hZB hz)))
      (fun h => Or.inr (hCrightZ g h z hz))
  have hrightM : ∀ g ∈ (B : Set G) ∪ reflectionCell U Z m,
      g * m ∈ (B : Set G) ∪ reflectionCell U Z m := by
    intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, ha, z, hz, b, hb, rfl⟩ := exists_reverse_factors hB hg
      right
      apply mem_reflectionCell_iff.mpr
      refine ⟨a, ha, m⁻¹ * z * m, hmZ z hz, m⁻¹ * b * m,
        hmV b (hplus hb), ?_⟩
      group
    · obtain ⟨a, ha, z, hz, b, hb, rfl⟩ := mem_reflectionCell_iff.mp hg
      have hzm : m * z * m ∈ Z := by
        have h := Z.mul_mem hsq (hmZ z hz)
        convert h using 1
        group
      have heq : a * m * z * b * m =
          a * (m * z * m) * (m⁻¹ * b * m) := by group
      rw [heq]
      rcases hV (hmU b hb) with hc | hc
      · left
        exact B.mul_mem (B.mul_mem (hUB ha) (hZB hzm)) (hplusB hc)
      · right
        exact hCleftUZ a ha (m * z * m) hzm _ hc
  have hrightMinv : ∀ g ∈ (B : Set G) ∪ reflectionCell U Z m,
      g * m⁻¹ ∈ (B : Set G) ∪ reflectionCell U Z m := by
    intro g hg
    have h := hrightZ (g * m) (hrightM g hg) (m ^ 2)⁻¹ (Z.inv_mem hsq)
    convert h using 1
    group
  have hrightV : ∀ g ∈ (B : Set G) ∪ reflectionCell U Z m, ∀ b ∈ V,
      g * b ∈ (B : Set G) ∪ reflectionCell U Z m := by
    intro g hg b hb
    have h := hrightMinv ((g * m) * (m⁻¹ * b * m))
      (hrightU (g * m) (hrightM g hg) _ (hmV b hb))
    convert h using 1
    group
  apply Set.Subset.antisymm
  · intro g hg
    have hclosure : U ⊔ V ⊔ Z =
        Subgroup.closure (((U : Set G) ∪ (V : Set G)) ∪ (Z : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_union,
        Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [SetLike.mem_coe, hclosure] at hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact Or.inl B.one_mem
    | mul_right x _ y hy ih =>
      rcases hy with (hy | hy) | hy
      · exact hrightU x ih y hy
      · exact hrightV x ih y hy
      · exact hrightZ x ih y hy
    | mul_inv_cancel x _ y hy ih =>
      rcases hy with (hy | hy) | hy
      · exact hrightU x ih y⁻¹ (U.inv_mem hy)
      · exact hrightV x ih y⁻¹ (V.inv_mem hy)
      · exact hrightZ x ih y⁻¹ (Z.inv_mem hy)
  · have hU : U ≤ U ⊔ V ⊔ Z := le_sup_left.trans le_sup_left
    have hV' : V ≤ U ⊔ V ⊔ Z := le_sup_right.trans le_sup_left
    have hZ : Z ≤ U ⊔ V ⊔ Z := le_sup_right
    intro g hg
    rcases hg with hg | hg
    · rw [hB] at hg
      obtain ⟨_, ⟨b, hb, z, hz, rfl⟩, a, ha, rfl⟩ := hg
      exact mul_mem (mul_mem (hV' (hplus hb)) (hZ hz)) (hU ha)
    · obtain ⟨a, ha, z, hz, b, hb, rfl⟩ := mem_reflectionCell_iff.mp hg
      exact mul_mem (mul_mem (mul_mem (hU ha) hm) (hZ hz)) (hU hb)

end Langlands.Group.FilteredRankOne
