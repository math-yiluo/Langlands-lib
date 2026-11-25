# Completeness of the irreducible characters of a finite group

This module states `Langlands.FiniteRep.FiniteCharacterCompletenessStatement`, a proposition
definition. Its proof is `Langlands.FiniteRep.CharacterCompleteness.finiteCharacterCompleteness`
(`CharacterCompletenessProof`).

## Statement

```lean
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
```

The notions are those of the Library's finite-group representation theory:

- `IrreducibleClass G` (`BrauerStatement`): isomorphism classes of finite-dimensional complex
  representations (`RepClass ℂ G`, `Classes`) with an irreducible representative;
- `character : RepClass ℂ G → G → ℂ` (`Classes`), the trace character of a representative;
- `virtualCharacters` (`Virtual`): the image of the Grothendieck group `VirtualRep ℂ G` under the
  character, that is, the differences of two characters;
- the pairing `|G|⁻¹ Σ_g χ(g⁻¹) f(g)` is the one of `CharacterStatement` and of
  `VirtualCharacter.pairing` (`VirtualCharacterProof`);
- a class function is written as the hypothesis `∀ g h, f (h * g * h⁻¹) = f g`, as in
  `character_conj` (`Classes`) and `CharacterStatement`.

In words, for a finite group `G`:

1. there are finitely many classes of irreducible complex representations, and as many as
   conjugacy classes of `G`;
2. the irreducible characters span the complex class functions;
3. a class function whose pairing with every irreducible character is an integer is a virtual
   character;
4. a class function whose pairing with every irreducible character is a natural number is the
   character of a representation.

## Declarations

- `FiniteCharacterCompletenessStatement` (definition, `Prop`).

## Literature

Jean-Pierre Serre, *Linear Representations of Finite Groups*, Graduate Texts in Mathematics 42,
Springer, 1977 (`/srv/central-library/Serre--Linear Representations of Finite Groups--1977.pdf`):

- §2.5, Theorem 6 (printed p. 19): the irreducible characters form an orthonormal basis of the space
  of class functions — clause 2 (the Library states the spanning; orthonormality is
  `VirtualCharacter.pairing_irreducible`);
- §2.5, Theorem 7 (printed pp. 19–20): the number of irreducible representations equals the number
  of classes — clause 1;
- §9.1 (printed p. 68): a class function is a character if and only if it is a linear combination
  of the irreducible characters with non-negative integer coefficients, and `R(G) = ⊕ ℤχ_i` —
  clauses 3 and 4, read through the expansion `f = Σ ⟨χ_i, f⟩ χ_i` of Theorem 6.

(PDF page = printed page + 9 in Part I, + 8 in Part II of this copy; checked on PDF pages 27–29
and 76.)
