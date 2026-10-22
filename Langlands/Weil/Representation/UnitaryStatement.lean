import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.Dual
import Langlands.Weil.Representation.Twist

/-!
# Unitarizability under equivalence, duality and unitary twists

These proposition targets use the published existential invariant positive
Hermitian form predicate and the actual finite-dimensional constructions.
No form, preservation proof or permutation of classes is supplied as input.
-/

namespace Langlands.FiniteRepresentation

universe uG uV uU

/-- Unitarizability is invariant under genuine representation equivalences,
including equivalences between independent carrier universes. -/
def UnitaryIsomorphismInvariance : Prop :=
  ∀ (G : Type uG) [Group G]
    (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (B : FiniteRepresentation.{0, uG, uU} ℂ G),
    Nonempty (Equiv A B) → (IsUnitary A ↔ IsUnitary B)

/-- A finite-dimensional representation is unitarizable exactly when its full
algebraic dual, with the inverse-element action, is unitarizable. -/
def UnitaryDuality : Prop :=
  ∀ (G : Type uG) [Group G]
    (A : FiniteRepresentation.{0, uG, uV} ℂ G),
    IsUnitary (dual A) ↔ IsUnitary A

/-- Twisting by a pointwise modulus-one character preserves and reflects
unitarizability. No topology is needed for this algebraic assertion. -/
def UnitaryTwisting : Prop :=
  ∀ (G : Type uG) [Group G]
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (χ : G →* ℂˣ),
    (∀ g : G, ‖(χ g : ℂ)‖ = 1) →
      (IsUnitary (twist χ A) ↔ IsUnitary A)

/-- The complete unitary operation family on actual finite-dimensional
representations, with all three universes independent. -/
def UnitaryOperations : Prop :=
  UnitaryIsomorphismInvariance.{uG, uV, uU} ∧
  UnitaryDuality.{uG, uV} ∧
  UnitaryTwisting.{uG, uV}

end Langlands.FiniteRepresentation
