# Proof of the unit criterion for normalized Artin maps

Module `Langlands.Global.Arithmetic.FiniteArtinUnramifiedCriterionProof`, name space
`Langlands.Global`. It proves the published `FiniteArtinUnramifiedCriterionStatement` of
[`FiniteArtinUnramifiedCriterion`](FiniteArtinUnramifiedCriterion.lean), from the bridge modules
`Langlands/ClassFieldTheory/Global/Artin/` onto the NYLL library (the copy under `Nyll/`). It
imports nothing of the copy directly.

## Main declaration

```lean
theorem finiteArtinUnramifiedCriterion : FiniteArtinUnramifiedCriterionStatement.{uK, uE}
```

The statement, as published (not changed):

```lean
def FiniteArtinUnramifiedCriterionStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K]
    (E : Type uE) [Field E] [NumberField E] [Algebra K E] [IsGalois K E],
    (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) →
    letI : TopologicalSpace (E ≃ₐ[K] E) := ⊥
    ∀ (ρ : IdeleClasses K →ₜ* (E ≃ₐ[K] E)),
      Function.Surjective ρ → HasArithmeticArtinNormalization ρ.toMonoidHom →
      ∀ v : FinitePlace K,
        (∀ a : (FiniteCompletion K v)ˣ,
          a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units →
          ρ (finiteClassInclusion K v a) = 1) →
        ∀ w : FinitePlace E, w.asIdeal.LiesOver v.asIdeal →
          Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) w.asIdeal
```

In words: for a finite abelian extension of number fields `E / K` and a continuous surjective
homomorphism `ρ` from the idèle classes of `K` to `Gal(E/K)` with the discrete topology that
satisfies the Library's arithmetic normalization (`HasArithmeticArtinNormalization`, from
`ClassFieldStatement`), if `ρ` kills the local units at a finite place `v`, then every prime of `E`
above `v` is unramified over `K`. The theorem has the statement as its type, with the same two
universe parameters in the same order.

Lean reports that `Langlands.Global.finiteArtinUnramifiedCriterion` depends on `propext`,
`Classical.choice` and `Quot.sound` only.

## Proof

`FiniteDimensional K E` follows from the two `NumberField` instances and `IsAbelianGalois K E`
from `IsGalois K E` and the commutativity hypothesis. By the uniqueness of a continuous
normalized map (`eq_of_hasArithmeticArtinNormalization`, `ArtinUniqueness`, which uses only the
Library), `ρ` is the arithmetic Artin map `arithmeticFiniteArtinBot K E`, normalized by
`arithmeticFiniteArtin_hasArithmeticArtinNormalization` (`FiniteArtinNormalization`). So the
arithmetic Artin map kills the local units at `v`, and
`isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one` (`FiniteArtinUnramified`)
gives that every prime above `v` is unramified. The surjectivity hypothesis is not used: the
normalization alone determines `ρ`.

## Declarations used

From the Library: `eq_of_hasArithmeticArtinNormalization` (`ArtinUniqueness`);
`arithmeticFiniteArtinBot` (`FiniteArtin`); `arithmeticFiniteArtin_hasArithmeticArtinNormalization`
(`FiniteArtinNormalization`); `isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one`
(`FiniteArtinUnramified`). The NYLL theorems behind the last one are listed on its page.

## Sources

Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter VI, Corollary (5.8), p. 394,
Proposition (6.5), p. 397, and Corollary (6.6), p. 398, with Chapter V, Proposition (1.7), p. 323
(see the page of `FiniteArtinUnramified`); the identification of a normalized map with the Artin
map is the uniqueness argument of `ArtinUniqueness` (see its page).
