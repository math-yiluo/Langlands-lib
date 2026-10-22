import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Semisimple

/-!
# Finite complex character theory used by Henniart

These are proposition definitions, not proofs of the propositions.
The representations, invariant subspaces, direct sums, characters, and
intertwining equivalences are the concrete Mathlib constructions.
-/

noncomputable section

namespace Langlands

universe uG uV uW

/-- Trace, inverse, conjugacy, and dual normalizations for finite-group characters. -/
def FiniteCharacterNormalizationStatement
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] : Prop :=
  ∀ ρ : Representation ℂ G V,
    ρ.character 1 = (Module.finrank ℂ V : ℂ) ∧
    (∀ g : G, ρ.character g⁻¹ = star (ρ.character g)) ∧
    (∀ g h : G, ρ.character (h * g * h⁻¹) = ρ.character g) ∧
    (∀ g : G, ρ.dual.character g = ρ.character g⁻¹)

/-- Every invariant subspace has an invariant complement, and every representation
is isomorphic to a finite direct sum of irreducible subrepresentations. -/
def FiniteCompleteReducibilityStatement
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] : Prop :=
  ∀ ρ : Representation ℂ G V,
    Representation.IsSemisimpleRepresentation ρ ∧
    ∃ (n : ℕ) (S : Fin n → Subrepresentation ρ),
      (∀ i, Representation.IsIrreducible (S i).toRepresentation) ∧
      Nonempty (Representation.Equiv
        (Representation.directSum (fun i => (S i).toRepresentation)) ρ)

/-- The inverse-character pairing is the complex image of the dimension of
the space of intertwiners from the first representation to the second. -/
def FiniteCharacterHomDimensionStatement
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] : Prop :=
  ∀ (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, ρ.character g⁻¹ * σ.character g =
      (Module.finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ)

/-- Isomorphic irreducibles have pairing one; nonisomorphic irreducibles
have pairing zero. Irreducibility is a hypothesis inside the proposition. -/
def FiniteCharacterOrthogonalityStatement
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] : Prop :=
  ∀ (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    Representation.IsIrreducible ρ →
    Representation.IsIrreducible σ →
    (Nonempty (Representation.Equiv ρ σ) →
      (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, ρ.character g⁻¹ * σ.character g = 1) ∧
    (¬ Nonempty (Representation.Equiv ρ σ) →
      (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, ρ.character g⁻¹ * σ.character g = 0)

/-- Equality of trace characters is equivalent to a genuine intertwining
linear equivalence, with independent universes for the two carriers. -/
def FiniteCharacterIsomorphismStatement
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] : Prop :=
  ∀ (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    ρ.character = σ.character ↔ Nonempty (Representation.Equiv ρ σ)

/-- A genuine representation is irreducible exactly when its character has
normalized squared norm one. The zero representation is permitted. -/
def FiniteCharacterNormOneStatement
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] : Prop :=
  ∀ ρ : Representation ℂ G V,
    (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, ρ.character g⁻¹ * ρ.character g = 1 ↔
      Representation.IsIrreducible ρ

/-- The coherent finite-dimensional complex character-theory prerequisites.
No conjunct is assumed as a field, instance, or theorem in this definition. -/
def FiniteCharacterTheoryStatement
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] : Prop :=
  FiniteCharacterNormalizationStatement G V ∧
  FiniteCharacterNormalizationStatement G W ∧
  FiniteCompleteReducibilityStatement G V ∧
  FiniteCompleteReducibilityStatement G W ∧
  FiniteCharacterHomDimensionStatement G V W ∧
  FiniteCharacterOrthogonalityStatement G V W ∧
  FiniteCharacterIsomorphismStatement G V W ∧
  FiniteCharacterNormOneStatement G V ∧
  FiniteCharacterNormOneStatement G W

end Langlands
