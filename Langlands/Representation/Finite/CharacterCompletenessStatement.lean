import Langlands.Representation.Finite.BrauerStatement
import Mathlib.Algebra.Group.ConjFinite

/-!
# Completeness of the irreducible characters of a finite group

The characters of the irreducible complex representations of a finite group span the class
functions, there are as many irreducible classes as conjugacy classes, and a class function is a
virtual character, resp. the character of a representation, when its pairing with every
irreducible character is an integer, resp. a natural number. Proposition definition only.
-/

noncomputable section

namespace Langlands.FiniteRep

universe uG

/-- **Completeness of the irreducible characters** of a finite group `G`, for class functions
`f : G → ℂ` (`f (h * g * h⁻¹) = f g`) and the pairing `|G|⁻¹ Σ_g χ(g⁻¹) f(g)`:

1. there are finitely many irreducible classes, as many as conjugacy classes;
2. every class function is a complex linear combination of irreducible characters;
3. a class function whose pairing with every irreducible character is an integer is a virtual
   character;
4. a class function whose pairing with every irreducible character is a natural number is the
   character of a representation. -/
def FiniteCharacterCompletenessStatement (G : Type uG) [Group G] [Fintype G] : Prop :=
  Finite (IrreducibleClass G) ∧
  Nat.card (IrreducibleClass G) = Nat.card (ConjClasses G) ∧
  (∀ f : G → ℂ, (∀ g h : G, f (h * g * h⁻¹) = f g) →
    f ∈ Submodule.span ℂ (Set.range fun a : IrreducibleClass G => character a.1)) ∧
  (∀ f : G → ℂ, (∀ g h : G, f (h * g * h⁻¹) = f g) →
    (∀ a : IrreducibleClass G,
      ∃ n : ℤ, (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character a.1 g⁻¹ * f g = n) →
    f ∈ virtualCharacters (k := ℂ) (G := G)) ∧
  (∀ f : G → ℂ, (∀ g h : G, f (h * g * h⁻¹) = f g) →
    (∀ a : IrreducibleClass G,
      ∃ n : ℕ, (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character a.1 g⁻¹ * f g = n) →
    ∃ c : RepClass ℂ G, character c = f)

end Langlands.FiniteRep
