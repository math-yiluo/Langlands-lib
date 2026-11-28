import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction
import Mathlib.Order.JordanHolder

/-! # Composition series of compact- and Lie-stable submodules -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uK uL uV

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The complex subspaces invariant under both the compact and Lie actions. -/
abbrev GKStableSubspaces := {W : Submodule ℂ V // IsGKSubmodule ρ π W}

namespace GKStableSubspaces

instance : Min (GKStableSubspaces ρ π) :=
  ⟨fun W N => ⟨W.val ⊓ N.val, ⟨fun k v hv => ⟨W.prop.1 k v hv.1, N.prop.1 k v hv.2⟩,
    fun X v hv => ⟨W.prop.2 X v hv.1, N.prop.2 X v hv.2⟩⟩⟩⟩

instance : Max (GKStableSubspaces ρ π) :=
  ⟨fun W N => ⟨W.val ⊔ N.val, ⟨fun k v hv => by
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (W.prop.1 k w hw) (N.prop.1 k z hz), fun X v hv => by
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (W.prop.2 X w hw) (N.prop.2 X z hz)⟩⟩⟩

instance : Lattice (GKStableSubspaces ρ π) :=
  Function.Injective.lattice Subtype.val Subtype.val_injective .rfl .rfl
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : IsModularLattice (GKStableSubspaces ρ π) where
  sup_inf_le_assoc_of_le {W} N {Y} h :=
    sup_inf_le_assoc_of_le N.val (show W.val ≤ Y.val from h)

instance : OrderBot (GKStableSubspaces ρ π) where
  bot := ⟨⊥, ⟨fun k v hv => by
    have he : v = 0 := by simpa using hv
    simp [he], fun X v hv => by
    have he : v = 0 := by simpa using hv
    simp [he]⟩⟩
  bot_le W := show (⊥ : Submodule ℂ V) ≤ W.val from bot_le

instance : OrderTop (GKStableSubspaces ρ π) where
  top := ⟨⊤, ⟨fun _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top⟩⟩
  le_top W := show W.val ≤ (⊤ : Submodule ℂ V) from le_top

@[simp] theorem val_sup (W N : GKStableSubspaces ρ π) : (W ⊔ N).val = W.val ⊔ N.val := rfl

@[simp] theorem val_inf (W N : GKStableSubspaces ρ π) : (W ⊓ N).val = W.val ⊓ N.val := rfl

@[simp] theorem val_bot : (⊥ : GKStableSubspaces ρ π).val = ⊥ := rfl

@[simp] theorem val_top : (⊤ : GKStableSubspaces ρ π).val = ⊤ := rfl

end GKStableSubspaces

private theorem exists_compSeries {X : Type*} [Lattice X] [IsModularLattice X]
    (h₁ : WellFoundedLT X) (h₂ : WellFoundedGT X) (a : X) :
    ∀ b : X, a ≤ b → ∃ s : CompositionSeries X, s.head = a ∧ s.last = b := by
  intro b
  induction b using h₁.induction with
  | ind b ih =>
    intro hab
    rcases eq_or_lt_of_le hab with rfl | hab
    · exact ⟨RelSeries.singleton _ a, rfl, rfl⟩
    · obtain ⟨c, hc, hmax⟩ := h₂.has_min {c : X | a ≤ c ∧ c < b}
        ⟨a, le_rfl, hab⟩
      have hcb : c ⋖ b := ⟨hc.2, fun {d} hcd hdb => hmax d
        ⟨hc.1.trans hcd.le, hdb⟩ hcd⟩
      obtain ⟨s, hsa, hsc⟩ := ih c hc.2 hc.1
      have hs : JordanHolderLattice.IsMaximal s.last b := by
        change s.last ⋖ b
        rwa [hsc]
      exact ⟨s.snoc b hs, by simpa only [RelSeries.head_snoc] using hsa,
        RelSeries.last_snoc _ _ _⟩

/-- When both chain conditions hold, each invariant interval has a finite
composition series. The modular lattice supplies the Jordan–Hölder relation. -/
def GKCompositionSeriesStatement : Prop :=
  WellFoundedLT (GKStableSubspaces ρ π) → WellFoundedGT (GKStableSubspaces ρ π) →
    ∀ W N : GKStableSubspaces ρ π, W ≤ N →
      ∃ s : CompositionSeries (GKStableSubspaces ρ π), s.head = W ∧ s.last = N

theorem gkCompositionSeries : GKCompositionSeriesStatement ρ π :=
  fun h₁ h₂ W N h => exists_compSeries h₁ h₂ W N h

end Langlands.Archimedean
