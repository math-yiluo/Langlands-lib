import Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferStatement

namespace Langlands.Classification

universe uK uG uH uV uW

private theorem nonbottom_inf_transport
    {α β : Type*} [SemilatticeInf α] [OrderBot α]
    [SemilatticeInf β] [OrderBot β] (e : α ≃o β)
    (h : ∀ a b : α, a ≠ ⊥ → b ≠ ⊥ → a ⊓ b ≠ ⊥) :
    ∀ a b : β, a ≠ ⊥ → b ≠ ⊥ → a ⊓ b ≠ ⊥ := by
  intro a b ha hb hab
  apply h (e.symm a) (e.symm b)
  · intro hbot
    exact ha (by simpa only [e.apply_symm_apply, e.map_bot] using congrArg e hbot)
  · intro hbot
    exact hb (by simpa only [e.apply_symm_apply, e.map_bot] using congrArg e hbot)
  · simpa only [e.symm.map_inf, e.symm.map_bot] using congrArg e.symm hab

private theorem nonbottom_inf_essential_interval
    {α : Type*} [Lattice α] [OrderBot α] (u : α) (hu : u ≠ ⊥) :
    (∀ a b : α, a ≠ ⊥ → b ≠ ⊥ → a ⊓ b ≠ ⊥) ↔
      (∀ a : α, a ≠ ⊥ → u ⊓ a ≠ ⊥) ∧
        (∀ a b : Set.Iic u, a ≠ ⊥ → b ≠ ⊥ → a ⊓ b ≠ ⊥) := by
  constructor
  · intro h
    refine ⟨fun a ha => h u a hu ha, ?_⟩
    intro a b ha hb hab
    apply h a.val b.val
    · intro hbot
      exact ha (Subtype.ext hbot)
    · intro hbot
      exact hb (Subtype.ext hbot)
    · exact congrArg Subtype.val hab
  · rintro ⟨hess, hint⟩ a b ha hb hab
    let a' : Set.Iic u := ⟨u ⊓ a, inf_le_left⟩
    let b' : Set.Iic u := ⟨u ⊓ b, inf_le_left⟩
    apply hint a' b'
    · intro hbot
      exact hess a ha (congrArg Subtype.val hbot)
    · intro hbot
      exact hess b hb (congrArg Subtype.val hbot)
    · apply Subtype.ext
      exact le_bot_iff.mp (hab ▸ inf_le_inf inf_le_right inf_le_right)

variable {k : Type uK} [Field k] {G : Type uG} [Group G] {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k H W}

theorem stronglyIndecomposable_iff_of_orderIso
    (e : Subrepresentation ρ ≃o Subrepresentation σ) :
    IsStronglyIndecomposable ρ ↔ IsStronglyIndecomposable σ :=
  ⟨nonbottom_inf_transport e, nonbottom_inf_transport e.symm⟩

theorem stronglyIndecomposable_iff_essential_interval
    (U : Subrepresentation ρ) (hU : U ≠ ⊥)
    (e : Subrepresentation σ ≃o Set.Iic U) :
    IsStronglyIndecomposable ρ ↔
      (∀ S : Subrepresentation ρ, S ≠ ⊥ → U ⊓ S ≠ ⊥) ∧
        IsStronglyIndecomposable σ := by
  rw [IsStronglyIndecomposable, nonbottom_inf_essential_interval U hU]
  exact and_congr_right fun _ =>
    ⟨nonbottom_inf_transport e.symm, nonbottom_inf_transport e⟩

theorem strongIndecomposabilityLatticeTransfer :
    StrongIndecomposabilityLatticeTransferStatement.{uK,uG,uH,uV,uW} := by
  intro k _ G _ H _ V _ _ W _ _ ρ σ
  exact ⟨stronglyIndecomposable_iff_of_orderIso,
    stronglyIndecomposable_iff_essential_interval⟩

end Langlands.Classification
