import Mathlib.RepresentationTheory.Intertwining

/-! # Pullback of representation equivalences

The existing general helper is shared by isotypic cohomology and quotient-invariant modules.
-/

noncomputable section

namespace Langlands.Cohomology.HyperextAbutment

variable {R : Type*} [CommRing R] {Γ Δ : Type*} [Group Γ] [Group Δ] {U V W : Type*}
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- An equivalence of representations of `Γ` is an equivalence of the representations of `Γ'`
obtained by composing with a group homomorphism `φ : Γ' →* Γ`. -/
def equivComp {Γ' : Type*} [Group Γ'] {ρ : Representation R Γ V} {σ : Representation R Γ W}
    (e : ρ.Equiv σ) (φ : Γ' →* Γ) : Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (φ g) v

end Langlands.Cohomology.HyperextAbutment
