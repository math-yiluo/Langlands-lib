import Langlands.Representation.Hecke.DoubleCosetSandwich
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.WellFoundedSet

/-!
# Products of mass-one double-coset indicators

Elementary facts about the mass-one indicators `a g = e_{K g K}` of a compact open subgroup
`K` of a Hausdorff topological group, used for Renard V.5.3: equality and linear independence,
finiteness over a compact set, exact products with elements normalizing `K`, a three-factor
product criterion (for Iwahori factorizations), Dickson's lemma with a finite label, and a
finite encoding of one-sided `K`-invariant subsets of a compact set.
-/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory TestFunction
open scoped Pointwise

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (μ : Measure G) [μ.IsHaarMeasure]

namespace HeckeAlgebra.Corner

omit [T2Space G] in
/-- Evaluation of corner elements at a point, as a linear functional. -/
def evalLinear (x : G) : Corner μ K hK →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [T2Space G] in
@[simp] theorem evalLinear_apply (x : G) (f : Corner μ K hK) : evalLinear K hK μ x f = f x :=
  rfl

theorem massIndicator_eq_of_mem {g a : G} (ha : a ∈ doubleCosetSet K g) :
    massIndicator K hK μ a = massIndicator K hK μ g := by
  apply ext' K hK μ
  intro x
  rw [massIndicator_apply, massIndicator_apply, doubleCosetSet_eq_of_mem K ha]

theorem massIndicator_apply_self_ne_zero (g : G) : massIndicator K hK μ g g ≠ 0 := by
  rw [massIndicator_apply, Set.indicator_of_mem (mem_doubleCosetSet_self K g)]
  simpa using doubleCosetSet_complex_mass_ne_zero K hK μ g

theorem massIndicator_apply_of_notMem {g x : G} (hx : x ∉ doubleCosetSet K g) :
    massIndicator K hK μ g x = 0 := by
  rw [massIndicator_apply, Set.indicator_of_notMem hx, mul_zero]

/-- Two mass-one indicators agree exactly when the double cosets agree. -/
theorem massIndicator_eq_iff {g₁ g₂ : G} :
    massIndicator K hK μ g₁ = massIndicator K hK μ g₂ ↔ g₁ ∈ doubleCosetSet K g₂ := by
  constructor
  · intro h
    by_contra hg
    apply massIndicator_apply_self_ne_zero K hK μ g₁
    rw [h]
    exact massIndicator_apply_of_notMem K hK μ hg
  · exact massIndicator_eq_of_mem K hK μ

/-- The mass-one indicators form a linearly independent set. -/
theorem linearIndepOn_range_massIndicator :
    LinearIndepOn ℂ id (Set.range (massIndicator K hK μ)) := by
  classical
  rw [LinearIndepOn, linearIndependent_iff']
  intro s c hs i hi
  obtain ⟨g, hg⟩ := i.property
  have hev := congrArg (evalLinear K hK μ g) hs
  rw [map_sum, map_zero] at hev
  rw [Finset.sum_eq_single i] at hev
  · simp only [map_smul, evalLinear_apply, id_eq, smul_eq_mul] at hev
    rw [← hg] at hev
    exact (mul_eq_zero.mp hev).resolve_right (massIndicator_apply_self_ne_zero K hK μ g)
  · intro b _ hbi
    simp only [map_smul, evalLinear_apply, id_eq, smul_eq_mul]
    obtain ⟨h, hh⟩ := b.property
    have : g ∉ doubleCosetSet K h := by
      intro hgh
      apply hbi
      apply Subtype.ext
      rw [← hh, ← hg]
      exact (massIndicator_eq_of_mem K hK μ hgh).symm
    rw [← hh, massIndicator_apply_of_notMem K hK μ this, mul_zero]
  · intro his
    exact absurd hi his

/-- Over a compact set there are only finitely many mass-one indicators. -/
theorem finite_image_massIndicator {S : Set G} (hS : IsCompact S) :
    (massIndicator K hK μ '' S).Finite := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun g : G => (fun y : G => g⁻¹ * y) ⁻¹' (K : Set G))
    (fun g => K.isOpen.preimage (continuous_const.mul continuous_id))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine ((t.finite_toSet.image (massIndicator K hK μ))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨g, hg, hgy⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨g, hg, (massIndicator_eq_of_mem K hK μ ?_).symm⟩
  exact (mem_doubleCosetSet K g y).2 ⟨1, K.one_mem, g⁻¹ * y, hgy, by group⟩

/-- Right product with an element whose inverse normalizes `K`. -/
theorem massIndicator_mul_of_normalizes {g x : G} (hx : ∀ k ∈ K, x⁻¹ * k * x ∈ K) :
    massIndicator K hK μ g * massIndicator K hK μ x = massIndicator K hK μ (g * x) := by
  apply massIndicator_mul K hK μ
  intro k hk
  exact (mem_doubleCosetSet K _ _).2 ⟨1, K.one_mem, x⁻¹ * k * x, hx k hk, by group⟩

/-- Left product with an element normalizing `K`. -/
theorem massIndicator_mul_of_normalizes' {g x : G} (hx : ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    massIndicator K hK μ x * massIndicator K hK μ g = massIndicator K hK μ (x * g) := by
  apply massIndicator_mul K hK μ
  intro k hk
  exact (mem_doubleCosetSet K _ _).2 ⟨x * k * x⁻¹, hx k hk, 1, K.one_mem, by group⟩

end HeckeAlgebra.Corner

namespace TestFunction

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] in
/-- Product criterion for a three-factor decomposition `K = P Q R`: if `g₁` conjugates `P` and
`Q` into `K` and `g₁ R g₂ ⊆ K g₁ g₂ K`, then `g₁ K g₂ ⊆ K g₁ g₂ K`. -/
theorem mul_mem_doubleCosetSet_of_factor_left {g₁ g₂ : G} (P Q R : Set G)
    (hdec : ∀ k ∈ K, ∃ p ∈ P, ∃ q ∈ Q, ∃ r ∈ R, k = p * q * r)
    (hP : ∀ p ∈ P, g₁ * p * g₁⁻¹ ∈ K) (hQ : ∀ q ∈ Q, g₁ * q * g₁⁻¹ ∈ K)
    (hR : ∀ r ∈ R, g₁ * r * g₂ ∈ doubleCosetSet K (g₁ * g₂)) :
    ∀ k ∈ K, g₁ * k * g₂ ∈ doubleCosetSet K (g₁ * g₂) := by
  intro k hk
  obtain ⟨p, hp, q, hq, r, hr, rfl⟩ := hdec k hk
  have h : g₁ * (p * q * r) * g₂ = (g₁ * p * g₁⁻¹) * ((g₁ * q * g₁⁻¹) * (g₁ * r * g₂)) := by
    group
  rw [h, mul_mem_doubleCosetSet_left K _ ⟨_, hP p hp⟩,
    mul_mem_doubleCosetSet_left K _ ⟨_, hQ q hq⟩]
  exact hR r hr

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] in
/-- Mirror product criterion: if `g₂⁻¹` conjugates `Q` and `R` into `K` and
`g₁ P g₂ ⊆ K g₁ g₂ K`, then `g₁ K g₂ ⊆ K g₁ g₂ K`. -/
theorem mul_mem_doubleCosetSet_of_factor_right {g₁ g₂ : G} (P Q R : Set G)
    (hdec : ∀ k ∈ K, ∃ p ∈ P, ∃ q ∈ Q, ∃ r ∈ R, k = p * q * r)
    (hQ : ∀ q ∈ Q, g₂⁻¹ * q * g₂ ∈ K) (hR : ∀ r ∈ R, g₂⁻¹ * r * g₂ ∈ K)
    (hP : ∀ p ∈ P, g₁ * p * g₂ ∈ doubleCosetSet K (g₁ * g₂)) :
    ∀ k ∈ K, g₁ * k * g₂ ∈ doubleCosetSet K (g₁ * g₂) := by
  intro k hk
  obtain ⟨p, hp, q, hq, r, hr, rfl⟩ := hdec k hk
  have h : g₁ * (p * q * r) * g₂ = (g₁ * p * g₂) * (g₂⁻¹ * q * g₂) * (g₂⁻¹ * r * g₂) := by
    group
  rw [h, mul_mem_doubleCosetSet_right K _ ⟨_, hR r hr⟩,
    mul_mem_doubleCosetSet_right K _ ⟨_, hQ q hq⟩]
  exact hP p hp

end TestFunction

/-- **Dickson's lemma with a finite label.** For a finite-coordinate vector `φ x` and a label
`V x` in a finite type, finitely many elements of `s` lie below every element of `s` with the
same label. -/
theorem exists_finite_le_of_label {X ι β : Type*} [Finite ι] [Finite β]
    (φ : X → ι → ℕ) (V : X → β) (s : Set X) :
    ∃ T : Set X, T.Finite ∧ T ⊆ s ∧ ∀ x ∈ s, ∃ t ∈ T, φ t ≤ φ x ∧ V t = V x := by
  classical
  let A : β → Set (ι → ℕ) := fun b => φ '' {y | y ∈ s ∧ V y = b}
  let M : β → Set (ι → ℕ) := fun b => {m | Minimal (· ∈ A b) m}
  have hMfin : ∀ b, (M b).Finite := fun b =>
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  have hpick : ∀ b, ∀ m : M b, ∃ y : X, (y ∈ s ∧ V y = b) ∧ φ y = m.val :=
    fun b m => m.property.1
  choose pick hpick_mem hpick_eq using hpick
  refine ⟨⋃ b, Set.range (pick b), Set.finite_iUnion fun b => ?_, ?_, ?_⟩
  · have := (hMfin b).to_subtype
    exact Set.finite_range _
  · intro t ht
    obtain ⟨b, m, rfl⟩ := Set.mem_iUnion.1 ht
    exact (hpick_mem b m).1
  · intro x hx
    obtain ⟨m, hmx, hm⟩ :=
      (Set.isPWO_of_wellQuasiOrderedLE (A (V x))).exists_le_minimal ⟨x, ⟨hx, rfl⟩, rfl⟩
    refine ⟨pick (V x) ⟨m, hm⟩, Set.mem_iUnion.2 ⟨V x, ⟨m, hm⟩, rfl⟩, ?_, ?_⟩
    · rw [hpick_eq]
      exact hmx
    · exact (hpick_mem _ _).2

omit [MeasurableSpace G] [BorelSpace G] [T2Space G] in
/-- Right-`K`-invariant subsets of a compact set are determined by finitely many test points. -/
theorem exists_finset_test_rightInvariant {W : Set G} (hW : IsCompact W) :
    ∃ t : Finset G, ∀ U₁ U₂ : Set G, U₁ ⊆ W → U₂ ⊆ W →
      (∀ u ∈ U₁, ∀ k ∈ K, u * k ∈ U₁) → (∀ u ∈ U₂, ∀ k ∈ K, u * k ∈ U₂) →
      (∀ g ∈ t, g ∈ U₁ ↔ g ∈ U₂) → U₁ = U₂ := by
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (fun g : G => (fun y : G => g⁻¹ * y) ⁻¹' (K : Set G))
    (fun g => K.isOpen.preimage (continuous_const.mul continuous_id))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine ⟨t, ?_⟩
  have key : ∀ U₁ U₂ : Set G, U₁ ⊆ W → (∀ u ∈ U₁, ∀ k ∈ K, u * k ∈ U₁) →
      (∀ u ∈ U₂, ∀ k ∈ K, u * k ∈ U₂) → (∀ g ∈ t, g ∈ U₁ ↔ g ∈ U₂) → U₁ ⊆ U₂ := by
    intro U₁ U₂ hU₁ hi₁ hi₂ hiff u hu
    obtain ⟨g, hg, hgu⟩ := Set.mem_iUnion₂.1 (ht (hU₁ hu))
    have hgu' : g⁻¹ * u ∈ K := hgu
    have hg₁ : g ∈ U₁ := by
      have := hi₁ u hu _ (K.inv_mem hgu')
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    have := hi₂ g ((hiff g hg).1 hg₁) _ hgu'
    rwa [mul_inv_cancel_left] at this
  intro U₁ U₂ hU₁ hU₂ hi₁ hi₂ hiff
  exact le_antisymm (key U₁ U₂ hU₁ hi₁ hi₂ hiff)
    (key U₂ U₁ hU₂ hi₂ hi₁ fun g hg => (hiff g hg).symm)

omit [MeasurableSpace G] [BorelSpace G] [T2Space G] in
/-- Left-`K`-invariant subsets of a compact set are determined by finitely many test points. -/
theorem exists_finset_test_leftInvariant {W : Set G} (hW : IsCompact W) :
    ∃ t : Finset G, ∀ U₁ U₂ : Set G, U₁ ⊆ W → U₂ ⊆ W →
      (∀ u ∈ U₁, ∀ k ∈ K, k * u ∈ U₁) → (∀ u ∈ U₂, ∀ k ∈ K, k * u ∈ U₂) →
      (∀ g ∈ t, g ∈ U₁ ↔ g ∈ U₂) → U₁ = U₂ := by
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (fun g : G => (fun y : G => y * g⁻¹) ⁻¹' (K : Set G))
    (fun g => K.isOpen.preimage (continuous_id.mul continuous_const))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine ⟨t, ?_⟩
  have key : ∀ U₁ U₂ : Set G, U₁ ⊆ W → (∀ u ∈ U₁, ∀ k ∈ K, k * u ∈ U₁) →
      (∀ u ∈ U₂, ∀ k ∈ K, k * u ∈ U₂) → (∀ g ∈ t, g ∈ U₁ ↔ g ∈ U₂) → U₁ ⊆ U₂ := by
    intro U₁ U₂ hU₁ hi₁ hi₂ hiff u hu
    obtain ⟨g, hg, hgu⟩ := Set.mem_iUnion₂.1 (ht (hU₁ hu))
    have hgu' : u * g⁻¹ ∈ K := hgu
    have hg₁ : g ∈ U₁ := by
      have := hi₁ u hu _ (K.inv_mem hgu')
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
    have := hi₂ g ((hiff g hg).1 hg₁) _ hgu'
    rwa [inv_mul_cancel_right] at this
  intro U₁ U₂ hU₁ hU₂ hi₁ hi₂ hiff
  exact le_antisymm (key U₁ U₂ hU₁ hi₁ hi₂ hiff)
    (key U₂ U₁ hU₂ hi₂ hi₁ fun g hg => (hiff g hg).symm)

end Langlands.Hecke
