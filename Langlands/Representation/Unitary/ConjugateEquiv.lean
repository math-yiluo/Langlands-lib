import Langlands.Representation.Unitary.Basic

/-!
# Invariant positive forms under conjugate-linear equivariant maps

Reversing the arguments of a pulled-back form compensates for conjugate
linearity. No norm, topology or finite dimension is required on the carriers.
-/

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

namespace InvariantPositiveForm

/-- Pull a positive invariant form back through an injective equivariant
conjugate-linear map, reversing its two arguments. -/
def conjugateComap (b : InvariantPositiveForm σ) (f : V →ₗ⋆[ℂ] W)
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = σ g (f v)) :
    InvariantPositiveForm ρ where
  inner v w := b.inner (f w) (f v)
  conj_inner_symm v w := b.conj_inner_symm (f w) (f v)
  re_inner_nonneg v := b.re_inner_nonneg (f v)
  add_left v w x := by
    let := b.toInnerProductCore
    change b.inner (f x) (f (v + w)) = _
    rw [map_add]
    exact InnerProductSpace.Core.inner_add_right (f x) (f v) (f w)
  smul_left v w c := by
    let := b.toInnerProductCore
    change b.inner (f w) (f (c • v)) = _
    rw [map_smulₛₗ]
    exact InnerProductSpace.Core.inner_smul_right (f w) (f v)
  definite v hv := hf <| by simpa using b.definite (f v) hv
  invariant g v w := by
    rw [he, he, b.invariant]

@[simp]
theorem conjugateComap_inner (b : InvariantPositiveForm σ) (f : V →ₗ⋆[ℂ] W)
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = σ g (f v)) (v w : V) :
    (b.conjugateComap f hf he).inner v w = b.inner (f w) (f v) := rfl

end InvariantPositiveForm

/-- Conjugate-linear equivariant injections preserve unitarizability by
pullback, with conjugation of the Hermitian form. -/
theorem IsUnitarizable.of_conjugate_injective (hσ : IsUnitarizable σ)
    (f : V →ₗ⋆[ℂ] W) (hf : Function.Injective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) : IsUnitarizable ρ := by
  obtain ⟨b⟩ := hσ
  exact ⟨b.conjugateComap f hf he⟩

/-- An equivariant conjugate-linear equivalence preserves and reflects the
existence of an invariant positive Hermitian form. -/
theorem isUnitarizable_iff_of_conjugateEquiv (e : V ≃ₗ⋆[ℂ] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    IsUnitarizable ρ ↔ IsUnitarizable σ := by
  have he' (g : G) (w : W) : e.symm (σ g w) = ρ g (e.symm w) := by
    apply e.injective
    simp only [e.apply_symm_apply, he]
  constructor
  · intro hρ
    exact hρ.of_conjugate_injective e.symm.toLinearMap e.symm.injective he'
  · intro hσ
    exact hσ.of_conjugate_injective e.toLinearMap e.injective he

end Langlands
