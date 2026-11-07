import Langlands.Representation.Smooth.CompactCompletion
import Langlands.Representation.Jacquet.StablePairingProof

/-!
# Completion restricted to a cofinal family

Compatible families on a set of compact open subgroups determine the full
completion when that set is cofinal under reverse inclusion. Extension at `K`
averages a component indexed by any member of the family contained in `K`.
-/

noncomputable section

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A family is cofinal for completion if each compact open subgroup contains
a member of the family. -/
def IsCofinal (S : Set (CompactOpenSubgroup G)) : Prop :=
  ∀ K : CompactOpenSubgroup G, ∃ L ∈ S, L.1 ≤ K.1

/-- Compatible completion families indexed only by `S`. -/
def completionOn (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (S : Set (CompactOpenSubgroup G)) : Submodule ℂ (S → V) where
  carrier := {v | ∀ K L : S, L.1.1 ≤ K.1.1 →
    Compact.averageMap ρ hρ K.1.1 K.1.2 (v L) = v K}
  zero_mem' := by
    intro K L _
    simp
  add_mem' := by
    intro a b ha hb K L hLK
    simp only [Pi.add_apply, map_add, ha K L hLK, hb K L hLK]
  smul_mem' := by
    intro c a ha K L hLK
    simp only [Pi.smul_apply, map_smul, ha K L hLK]

variable {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
variable (S : Set (CompactOpenSubgroup G))

/-- Restriction of a full completion family to `S`. -/
def restrict : completion ρ hρ →ₗ[ℂ] completionOn ρ hρ S where
  toFun v := ⟨fun K => v.1 K.1, fun K L hLK => v.property K.1 L.1 hLK⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrict_apply (v : completion ρ hρ) (K : S) :
    (restrict hρ S v).1 K = v.1 K.1 :=
  rfl

private def indexBelow (hS : IsCofinal S) (K : CompactOpenSubgroup G) : S :=
  ⟨(hS K).choose, (hS K).choose_spec.1⟩

omit [IsTopologicalGroup G] in
private theorem indexBelow_le (hS : IsCofinal S) (K : CompactOpenSubgroup G) :
    (indexBelow S hS K).1.1 ≤ K.1 :=
  (hS K).choose_spec.2

/-- Averaging to `K` is independent of the chosen smaller index in a cofinal
family. A third index below the intersection compares the two choices. -/
theorem average_component_eq (hS : IsCofinal S) (v : completionOn ρ hρ S)
    (K : CompactOpenSubgroup G) (L₁ L₂ : S)
    (h₁ : L₁.1.1 ≤ K.1) (h₂ : L₂.1.1 ≤ K.1) :
    Compact.averageMap ρ hρ K.1 K.2 (v.1 L₁) =
      Compact.averageMap ρ hρ K.1 K.2 (v.1 L₂) := by
  let R := indexBelow S hS (L₁.1.inf L₂.1)
  have hR₁ : R.1.1 ≤ L₁.1.1 :=
    (indexBelow_le S hS _).trans inf_le_left
  have hR₂ : R.1.1 ≤ L₂.1.1 :=
    (indexBelow_le S hS _).trans inf_le_right
  rw [← v.property L₁ R hR₁, ← v.property L₂ R hR₂,
    Jacquet.averageMap_averageMap_of_le ρ hρ K.1 L₁.1.1 K.2 L₁.1.2 h₁,
    Jacquet.averageMap_averageMap_of_le ρ hρ K.1 L₂.1.1 K.2 L₂.1.2 h₂]

private def extendFamily (hS : IsCofinal S) (v : completionOn ρ hρ S) :
    CompactOpenSubgroup G → V :=
  fun K => Compact.averageMap ρ hρ K.1 K.2 (v.1 (indexBelow S hS K))

private theorem extendFamily_eq (hS : IsCofinal S) (v : completionOn ρ hρ S)
    (K : CompactOpenSubgroup G) (L : S) (hLK : L.1.1 ≤ K.1) :
    extendFamily hρ S hS v K = Compact.averageMap ρ hρ K.1 K.2 (v.1 L) :=
  average_component_eq hρ S hS v K _ L (indexBelow_le S hS K) hLK

/-- Extend a compatible family on a cofinal set by averaging its components. -/
def extend (hS : IsCofinal S) : completionOn ρ hρ S →ₗ[ℂ] completion ρ hρ where
  toFun v := ⟨extendFamily hρ S hS v, by
    intro K L hLK
    rw [extendFamily_eq hρ S hS v K (indexBelow S hS L)
      ((indexBelow_le S hS L).trans hLK)]
    exact Jacquet.averageMap_averageMap_of_le ρ hρ K.1 L.1 K.2 L.2 hLK _⟩
  map_add' _ _ := by
    apply Subtype.ext
    funext K
    exact (Compact.averageMap ρ hρ K.1 K.2).map_add _ _
  map_smul' _ _ := by
    apply Subtype.ext
    funext K
    exact (Compact.averageMap ρ hρ K.1 K.2).map_smul _ _

/-- Any member of the family below `K` computes the extended `K`-component. -/
theorem extend_apply (hS : IsCofinal S) (v : completionOn ρ hρ S)
    (K : CompactOpenSubgroup G) (L : S) (hLK : L.1.1 ≤ K.1) :
    (extend hρ S hS v).1 K = Compact.averageMap ρ hρ K.1 K.2 (v.1 L) :=
  extendFamily_eq hρ S hS v K L hLK

@[simp]
theorem extend_restrict (hS : IsCofinal S) (v : completion ρ hρ) :
    extend hρ S hS (restrict hρ S v) = v := by
  apply Subtype.ext
  funext K
  exact v.property K (indexBelow S hS K).1 (indexBelow_le S hS K)

@[simp]
theorem restrict_extend (hS : IsCofinal S) (v : completionOn ρ hρ S) :
    restrict hρ S (extend hρ S hS v) = v := by
  apply Subtype.ext
  funext K
  change (extend hρ S hS v).1 K.1 = v.1 K
  rw [extend_apply hρ S hS v K.1 K le_rfl]
  exact v.property K K le_rfl

/-- Restricting completion families to a cofinal set is a linear equivalence. -/
def restrictEquiv (hS : IsCofinal S) :
    completion ρ hρ ≃ₗ[ℂ] completionOn ρ hρ S :=
  { restrict hρ S with
    invFun := extend hρ S hS
    left_inv := extend_restrict hρ S hS
    right_inv := restrict_extend hρ S hS }

@[simp]
theorem restrictEquiv_apply (hS : IsCofinal S) (v : completion ρ hρ) (K : S) :
    (restrictEquiv hρ S hS v).1 K = v.1 K.1 :=
  rfl

theorem restrictEquiv_symm_apply (hS : IsCofinal S) (v : completionOn ρ hρ S)
    (K : CompactOpenSubgroup G) (L : S) (hLK : L.1.1 ≤ K.1) :
    ((restrictEquiv hρ S hS).symm v).1 K =
      Compact.averageMap ρ hρ K.1 K.2 (v.1 L) :=
  extend_apply hρ S hS v K L hLK

end Langlands.CompactCompletion
