import Langlands.Representation.Unitary.Basic

/-! # Restriction of invariant positive forms

The generic form-restriction helpers from `Weil.Representation.UnitaryRestriction`,
with unchanged declarations and proofs, shared with tempered unitarity.
-/

noncomputable section

universe uG uH uJ uV

namespace Langlands

section Forms

variable {G : Type uG} {H : Type uH} {J : Type uJ}
  [Monoid G] [Monoid H] [Monoid J]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

namespace InvariantPositiveForm

/-- Restrict the same positive form along an arbitrary monoid homomorphism. -/
def comp (b : InvariantPositiveForm ρ) (φ : H →* G) :
    InvariantPositiveForm (ρ.comp φ) where
  toInnerProductCore := b.toInnerProductCore
  invariant h v w := b.invariant (φ h) v w

@[simp]
theorem comp_inner (b : InvariantPositiveForm ρ) (φ : H →* G) (v w : V) :
    (b.comp φ).inner v w = b.inner v w := rfl

@[simp]
theorem comp_id (b : InvariantPositiveForm ρ) :
    b.comp (MonoidHom.id G) = b := rfl

/-- Iterated precomposition retains precisely the same form. -/
theorem comp_comp (b : InvariantPositiveForm ρ) (φ : H →* G) (ψ : J →* H) :
    (b.comp φ).comp ψ = b.comp (φ.comp ψ) := rfl

end InvariantPositiveForm

/-- Unitarizability is preserved under restriction without topology assumptions. -/
theorem IsUnitarizable.comp (hρ : IsUnitarizable ρ) (φ : H →* G) :
    IsUnitarizable (ρ.comp φ) := by
  obtain ⟨b⟩ := hρ
  exact ⟨b.comp φ⟩

end Forms

end Langlands
