import Langlands.Representation.Hecke.DoubleCosetSandwich
import Langlands.Representation.Hecke.UniformFixedLevelBounds

/-! # Hecke sandwich data from an Iwahori factorization -/

noncomputable section

namespace Langlands.Hecke

universe uG

variable {G : Type uG} [Group G]

/-- The elements preserving the three intersection subgroups in the
directions needed for multiplication of positive double cosets. -/
def iwahoriPositiveMonoid (K N M Nbar : Subgroup G) : Submonoid G where
  carrier := {a |
    (∀ u ∈ K ⊓ N, a * u * a⁻¹ ∈ K ⊓ N) ∧
    (∀ l ∈ K ⊓ Nbar, a⁻¹ * l * a ∈ K ⊓ Nbar) ∧
    (∀ m ∈ K ⊓ M, a⁻¹ * m * a ∈ K ⊓ M)}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;> simpa using hx
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have h := ha.1 _ (hb.1 u hu)
      convert h using 1
      group
    · intro l hl
      have h := hb.2.1 _ (ha.2.1 l hl)
      convert h using 1
      group
    · intro m hm
      have h := hb.2.2 _ (ha.2.2 m hm)
      convert h using 1
      group

/-- Full central directions belong to the positive monoid, with no
restriction on the center or the root rank. -/
theorem center_le_iwahoriPositiveMonoid (K N M Nbar : Subgroup G) :
    (Subgroup.center G).toSubmonoid ≤ iwahoriPositiveMonoid K N M Nbar := by
  intro a ha
  have hac : ∀ x : G, x * a = a * x := Subgroup.mem_center_iff.mp ha
  have haic : ∀ x : G, x * a⁻¹ = a⁻¹ * x :=
    Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem ha)
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    simpa only [← hac u, mul_assoc, mul_inv_cancel, mul_one] using hu
  · intro l hl
    simpa only [← haic l, mul_assoc, inv_mul_cancel, mul_one] using hl
  · intro m hm
    simpa only [← haic m, mul_assoc, inv_mul_cancel, mul_one] using hm

variable [TopologicalSpace G]

namespace TestFunction

/-- Ordered Iwahori factorization and three one-sided conjugation bounds
give the literal double-coset containment needed for Hecke multiplication. -/
theorem mul_mem_doubleCosetSet_of_iwahori
    (K : OpenSubgroup G) (N M Nbar : Subgroup G)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.toSubgroup ⊓ M, ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (a b : G)
    (hup : ∀ u ∈ K.toSubgroup ⊓ N, a * u * a⁻¹ ∈ K)
    (hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, b⁻¹ * l * b ∈ K)
    (hmid : ∀ m ∈ K.toSubgroup ⊓ M, b⁻¹ * m * b ∈ K)
    (k : G) (hk : k ∈ K) :
    a * k * b ∈ doubleCosetSet K (a * b) := by
  obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := hfactor k⁻¹ (K.inv_mem hk)
  have hkprod : k = u⁻¹ * m⁻¹ * l⁻¹ := by
    rw [← inv_inv k, hprod]
    group
  refine (mem_doubleCosetSet K _ _).2
    ⟨a * u⁻¹ * a⁻¹, hup _ ((K.toSubgroup ⊓ N).inv_mem hu),
      (b⁻¹ * m⁻¹ * b) * (b⁻¹ * l⁻¹ * b),
      K.mul_mem (hmid _ ((K.toSubgroup ⊓ M).inv_mem hm))
        (hlow _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)), ?_⟩
  rw [hkprod]
  group

end TestFunction

variable [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

open MeasureTheory

/-- An actual compact-open Hecke corner has finite sandwich data when a
compact normalizing subgroup and finitely many commuting positive elements
supply a Cartan decomposition. All data are chosen before a representation. -/
theorem nonempty_fixedLevelSandwich_of_iwahoriCartan
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (μ : Measure G) [μ.IsHaarMeasure]
    (N M Nbar : Subgroup G)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.toSubgroup ⊓ M, ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (Γ : Subgroup G) (hΓc : IsCompact (Γ : Set G))
    (hΓ : Γ ≤ Subgroup.normalizer (K.toSubgroup : Set G))
    {r : ℕ} (D : Fin r → G)
    (hD : ∀ j, D j ∈ iwahoriPositiveMonoid K.toSubgroup N M Nbar)
    (hcomm : ∀ i j, Commute (D i) (D j))
    (hdecomp : ∀ g : G, ∃ γ ∈ Γ, ∃ γ' ∈ Γ,
      ∃ m ∈ Submonoid.closure (Set.range D), g = γ * m * γ') :
    Nonempty (FixedLevelSandwich μ K hK) := by
  have hmul : ∀ a ∈ iwahoriPositiveMonoid K.toSubgroup N M Nbar,
      ∀ b ∈ iwahoriPositiveMonoid K.toSubgroup N M Nbar,
      ∀ k ∈ K, a * k * b ∈ TestFunction.doubleCosetSet K (a * b) := by
    intro a ha b hb k hk
    exact TestFunction.mul_mem_doubleCosetSet_of_iwahori K N M Nbar hfactor a b
      (fun u hu => (ha.1 u hu).1)
      (fun l hl => (hb.2.1 l hl).1)
      (fun m hm => (hb.2.2 m hm).1) k hk
  obtain ⟨q, edge, middle, hmiddle, hspan⟩ :=
    HeckeAlgebra.Corner.exists_sandwich_of_decomposition K hK μ Γ hΓc hΓ
      (iwahoriPositiveMonoid K.toSubgroup N M Nbar) hmul D hD hcomm hdecomp
  exact ⟨⟨q, r, edge, middle, hmiddle, hspan⟩⟩

end Langlands.Hecke
