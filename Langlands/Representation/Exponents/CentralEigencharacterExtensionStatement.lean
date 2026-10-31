import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Exponents.Jacquet

/-!
# Extending generalized eigencharacters of a central action

A derived algebraic interface for a general admissible representation.
This module states a proposition and supplies no proof.
-/

namespace Langlands

universe uG uA uB uX

/-- Let a commutative topological group `A` act on an admissible representation
`π` of `G` through a continuous homomorphism `φ` with central image. A
generalized eigencharacter `χ` of the further pullback along `β : A' →* A` is
the restriction along `β` of a generalized eigencharacter `ψ` of the whole
action of `A` whose kernel is open. -/
def CentralEigencharacterExtensionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (A : Type uA) [CommGroup A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (A' : Type uB) [Monoid A']
    (X : Type uX) [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X), IsAdmissible π →
    ∀ φ : A →* G, Continuous φ → (∀ a g, Commute (φ a) g) →
    ∀ (β : A' →* A) (χ : A' →* ℂˣ),
      IsGeneralizedEigencharacter ((π.comp φ).comp β) χ →
      ∃ ψ : A →* ℂˣ, IsOpen (ψ.ker : Set A) ∧
        IsGeneralizedEigencharacter (π.comp φ) ψ ∧ ψ.comp β = χ

end Langlands
