import Langlands.Representation.Aubert.SubgroupTransition

/-! The initial actual subgroup term is canonically the original smooth module. -/

noncomputable section

set_option maxHeartbeats 1600000

namespace Langlands.Aubert.SubgroupTransition

open Jacquet.Localization

universe uR uG uV

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The full subgroup normalizes the trivial subgroup. -/
theorem top_normalizes_bot :
    (⊤ : Subgroup G) ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
  rw [Subgroup.normalizer_eq_top]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Trivial-character localization at the trivial subgroup has no relations. -/
theorem relations_bot (ρ : Representation R G V) :
    Jacquet.Localization.relations ρ ⊥ 1 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨⟨u, v⟩, rfl⟩
    have hu : (u : G) = 1 := (Subgroup.mem_bot).mp u.property
    simp [hu]
  · exact bot_le

/-- The orbit-function map into the initial full-group term is injective. -/
theorem initial_augmentation_injective (ρ : Representation R G V) (hρ : IsSmooth ρ) :
    Function.Injective (augmentation ⊤ ⊥ top_normalizes_bot ρ hρ) := by
  intro v w h
  have hvw := congrArg
    (fun f => Induction.eval ⊤ (inducing ⊤ ⊥ top_normalizes_bot ρ) f 1) h
  change mk ρ ⊥ 1 (ρ 1 v) = mk ρ ⊥ 1 (ρ 1 w) at hvw
  simp only [map_one, Module.End.one_apply] at hvw
  have hrel := (mk_eq_iff ρ ⊥ 1 v w).mp hvw
  rw [relations_bot] at hrel
  have hvw0 : v - w = 0 := by simpa using hrel
  exact sub_eq_zero.mp hvw0

/-- Covariance under the full group determines a function from its value at one. -/
theorem initial_augmentation_surjective (ρ : Representation R G V) (hρ : IsSmooth ρ) :
    Function.Surjective (augmentation ⊤ ⊥ top_normalizes_bot ρ hρ) := by
  intro f
  obtain ⟨v, hv⟩ := mk_surjective ρ (⊥ : Subgroup G) 1
    (Induction.eval ⊤ (inducing ⊤ ⊥ top_normalizes_bot ρ) f 1)
  refine ⟨v, ?_⟩
  ext g
  have hf := f.1.property (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) 1
  change Induction.eval ⊤ (inducing ⊤ ⊥ top_normalizes_bot ρ) f (g * 1) =
    inducing ⊤ ⊥ top_normalizes_bot ρ ⟨g, Subgroup.mem_top g⟩
      (Induction.eval ⊤ (inducing ⊤ ⊥ top_normalizes_bot ρ) f 1) at hf
  rw [mul_one, ← hv] at hf
  exact hf.symm

/-- The canonical representation equivalence from `E` to its initial function term. -/
def initialEquiv (ρ : Representation R G V) (hρ : IsSmooth ρ) :
    ρ.Equiv (term ⊤ ⊥ top_normalizes_bot ρ) :=
  (augmentation ⊤ ⊥ top_normalizes_bot ρ hρ).ofBijective
    ⟨initial_augmentation_injective ρ hρ, initial_augmentation_surjective ρ hρ⟩

@[simp]
theorem initialEquiv_eval (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (v : V) (g : G) :
    Induction.eval ⊤ (inducing ⊤ ⊥ top_normalizes_bot ρ) (initialEquiv ρ hρ v) g =
      mk ρ ⊥ 1 (ρ g v) := rfl

end Langlands.Aubert.SubgroupTransition
