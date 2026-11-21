import Langlands.Group.RelativeWeylConjugation
import Langlands.BushnellKutzko.RepresentationIntertwining

/-! # Conjugation and isomorphism of pairs `(J, λ)` -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uG uW uW₁ uW₂

variable {G : Type uG} [Group G]

theorem mem_conjSubgroup {g : G} {J : Subgroup G} {y : G} :
    y ∈ Langlands.Group.RelativeWeyl.conjugateSubgroup g J ↔ ∃ j ∈ J, g * j * g⁻¹ = y :=
  Iff.rfl

/-- The isomorphism `J ≃* g J g⁻¹`, `j ↦ g j g⁻¹`. -/
def conjSubgroupEquiv (g : G) (J : Subgroup G) : J ≃* Langlands.Group.RelativeWeyl.conjugateSubgroup g J :=
  J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

@[simp] theorem coe_conjSubgroupEquiv (g : G) (J : Subgroup G) (j : J) :
    (conjSubgroupEquiv g J j : G) = g * j * g⁻¹ :=
  rfl

variable {J : Subgroup G} {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The representation `λ^{g⁻¹}` of `g J g⁻¹`, given by `λ^{g⁻¹}(g j g⁻¹) = λ(j)`. -/
def conjRepresentation (g : G) (ρ : Representation ℂ J W) :
    Representation ℂ (Langlands.Group.RelativeWeyl.conjugateSubgroup g J) W :=
  ρ.comp (conjSubgroupEquiv g J).symm.toMonoidHom

@[simp] theorem conjRepresentation_conjSubgroupEquiv (g : G) (ρ : Representation ℂ J W)
    (j : J) : conjRepresentation g ρ (conjSubgroupEquiv g J j) = ρ j := by
  simp [conjRepresentation]

variable {J₁ J₂ : Subgroup G} {W₁ : Type uW₁} {W₂ : Type uW₂}
  [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

/-- Two pairs `(J₁, ρ₁)` and `(J₂, ρ₂)` are isomorphic when `J₁ = J₂` and the representations
are isomorphic as representations of this common group. -/
def IsPairIsomorphic (ρ₁ : Representation ℂ J₁ W₁) (ρ₂ : Representation ℂ J₂ W₂) : Prop :=
  ∃ h : J₁ = J₂,
    Nonempty (Representation.Equiv (ρ₁.comp (MulEquiv.subgroupCongr h).symm.toMonoidHom) ρ₂)

/-- Two pairs are `G`-conjugate when the second is isomorphic to `g · (J₁, ρ₁)` for some
`g ∈ G`. -/
def AreConjugatePairs (ρ₁ : Representation ℂ J₁ W₁) (ρ₂ : Representation ℂ J₂ W₂) : Prop :=
  ∃ g : G, IsPairIsomorphic (conjRepresentation g ρ₁) ρ₂

end Langlands.BushnellKutzko
