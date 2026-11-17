# Finite Galois character anti-equivalence for groups of multiplicative type: proof

Author: Worker 158.

This module proves the published proposition
`Langlands.GroupScheme.MultiplicativeTypeGaloisEquivalenceStatement.{u}`
(see [the statement](MultiplicativeTypeGaloisEquivalenceStatement.md)) as the
theorem

```text
theorem multiplicativeTypeGaloisEquivalence :
    MultiplicativeTypeGaloisEquivalenceStatement.{u}
```

for every universe `u`. The statement says: for fields `k L : Type u` with
`Algebra k L`, `FiniteDimensional k L` and `IsGalois k L`, the published actual
character functor
`SplitMultiplicativeType.characterFunctor k L :
(SplitMultiplicativeType k L)ᵒᵖ ⥤ Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L)`
is `Functor.IsEquivalence`. Torsion in the character groups is allowed; no
smoothness, connectedness, freeness or characteristic hypothesis appears.

## Proof

The proof is the single term

```text
multiplicativeTypeGaloisEquivalence_of_fullFaithfulness
  multiplicativeTypeGaloisFullFaithfulness
```

combining two results:

- `Langlands.GroupScheme.multiplicativeTypeGaloisEquivalence_of_fullFaithfulness`
  (module `Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisEquivalenceReduction`,
  submitted with this proof; see
  [the reduction](MultiplicativeTypeGaloisEquivalenceReduction.md)). It proves
  `MultiplicativeTypeGaloisFullFaithfulnessStatement.{u} →
  MultiplicativeTypeGaloisEquivalenceStatement.{u}`. Faithfulness and fullness
  of the character functor are derived from the hypothesis; essential
  surjectivity is proved unconditionally from the published realization theorem
  `Langlands.GroupScheme.multiplicativeTypeGaloisModuleRealization`
  (module `Langlands.GroupScheme.Torus.GaloisModuleRealizationProof`).
- `Langlands.GroupScheme.multiplicativeTypeGaloisFullFaithfulness`
  (published module
  `Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFullFaithfulnessProof`),
  the proof of the published proposition
  `Langlands.GroupScheme.MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}`:
  for actual commutative `k`-group schemes `T`, `T'` with specified
  isomorphisms of their base changes to diagonalizable `L`-groups of finitely
  generated abelian groups, an additive map of actual `L`-character groups is
  Galois-equivariant if and only if it is the character pullback of a unique
  actual `k`-homomorphism `T ⟶ T'`.

Both results are instantiated at the same universe `u`, so the theorem is
universe-polymorphic exactly as the statement. Lean reports that it depends only
on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement is the published finite-level derivation of J. S. Milne,
*Algebraic Groups* (2017), Theorem 12.23 (source `milne-2017-algebraic-groups`);
its own Markdown records the exact locator and the correspondence. The Lean
route is the one described in the context of Task 6926: the equivalence is
assembled as fully faithful plus essentially surjective, using the published
full-faithfulness and Galois-module realization theorems. The theorem is about
the published functor `SplitMultiplicativeType.characterFunctor k L` itself,
with its actual object and map assignments; it has no premise, and the separately
owned exact-sequence compatibility (Task 6657) is neither used nor proved here.
