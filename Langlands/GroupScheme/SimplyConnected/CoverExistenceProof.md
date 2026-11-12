# Proof: existence of simply connected central covers over arbitrary fields

Author: Worker 4027.

This module proves the published proposition
`Langlands.GroupScheme.SimplyConnectedCoverExistenceStatement`
([`CoverExistenceStatement`](CoverExistenceStatement.md)) at its original,
arbitrary universe `u`:

```
theorem simplyConnectedCoverExistence :
    SimplyConnectedCoverExistenceStatement.{u}
```

So for every field `k : Type u` and every actual group scheme `G` over
`Spec k` with `IsSemisimple G`, there are an actual group scheme `C` over
`Spec k` and an actual homomorphism `π : C ⟶ G` with
`IsSimplyConnectedCover π`. That predicate has four fields: `G` is
semisimple, `C` is algebraically simply connected, `π` is a central isogeny
with full scheme-theoretic kernel, and every central isogeny onto `G` from a
semisimple group receives a unique factorization of `π`.

The theorem adds no hypotheses. There is no perfectness, separable-closedness
or characteristic condition on `k`, and no chosen torus, root datum, pinning
or splitting of `G`. No cover, factorization law, lifting or base-change
property is taken as data. The module does not change the statement pair or
any pair it imports. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Implemented proof

The proof applies the published conditional reduction
`simplyConnectedCoverExistence_of_finiteGaloisInputs` from
[`FiniteGaloisExistenceReduction`](FiniteGaloisExistenceReduction.md). That
theorem derives the target from the seven-part bundle
`FiniteGaloisCoverExistenceInputsStatement.{u}`. Every component of the
bundle is now a published theorem. The module supplies them as follows.

1. `TorusFiniteGaloisSplittingStatement.{u}` is
   `torusFiniteGaloisSplitting`, from
   [`Torus.FiniteGaloisSplittingProof`](../Torus/FiniteGaloisSplittingProof.md):
   every torus over a field splits over a finite Galois extension.
2. `MaximalTorusBaseChangeStatement.{u}` is `maximalTorusBaseChange`, from
   [`Torus.MaximalBaseChangeProof`](../Torus/MaximalBaseChangeProof.md):
   a torus is maximal exactly when its base change to any field extension is
   maximal (Milne Theorem 17.82).
3. `SemisimpleFiniteGaloisAscentStatement.{u}` is the helper theorem
   `semisimpleFiniteGaloisAscent` of this module. It forgets the
   `FiniteDimensional` and `IsGalois` instances and applies
   `isSemisimpleFieldExtension`, from
   [`SemisimpleFieldExtensionProof`](SemisimpleFieldExtensionProof.md), which
   gives semisimplicity of the base change along an arbitrary field
   extension.
4. `SplitSimplyConnectedCoverExistenceStatement.{u}` is
   `splitSimplyConnectedCoverExistence`, from
   [`SplitCoverExistenceProof`](SplitCoverExistenceProof.md): a semisimple
   group with a split maximal torus has a simply connected group with a
   central isogeny onto it.
5. `SimplyConnectedCentralCoverUniversalProperty.{u}` is
   `simplyConnectedCentralCoverUniversalProperty`, from
   [`UniversalPropertyProof`](UniversalPropertyProof.md): a central isogeny
   from a simply connected group onto a semisimple group has the
   unique-factorization law.
6. `Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement.{u}` is
   `Langlands.FieldTheory.finiteGaloisTensorDecomposition`, from
   [`FieldTheory.FiniteGaloisTensorDecompositionProof`](../../FieldTheory/FiniteGaloisTensorDecompositionProof.md):
   for finite Galois `L/k` there is an `L`-algebra equivalence
   `L ⊗[k] L ≃ (Gal(L/k) → L)` with `a ⊗ b ↦ (σ ↦ a * σ b)`.
7. `SimplyConnectedCoverTensorDescentStatement.{u,u}` is
   `simplyConnectedCoverTensorDescent.{u,u}`, from
   [`Descent.TensorFullCoverProof`](../Descent/TensorFullCoverProof.md),
   with its index universe specialized to `u` as the bundle requires: a
   simply connected cover of `G_L` descends, through such a tensor
   decomposition, to a simply connected cover of `G`.

The theorem `finiteGaloisCoverExistenceInputs` packages these seven proofs
as the bundle, and `simplyConnectedCoverExistence` applies the reduction to
it.

For the reader, the route of the reduction (its Markdown has the details) is:
the base change of `G` to a suitable finite Galois extension `L/k` has a
split maximal torus (inputs 1 and 2 with the published maximal-torus
existence theorem); `G_L` is semisimple (input 3); the split case gives a
simply connected central isogeny `π : C ⟶ G_L` (input 4), which has the
unique-factorization law (input 5), so `IsSimplyConnectedCover π`; and the
tensor decomposition of `L ⊗[k] L` (input 6) lets this cover descend to an
actual `a : D ⟶ G` over `k` with `IsSimplyConnectedCover a` (input 7).

## Provenance

The statement is CGP, *Pseudo-reductive groups* (2015), Corollary
A.4.11(1), packaged with the universal property of Milne, *Algebraic Groups*
(2017), Proposition 18.8, as recorded in the statement's Markdown. The
implemented route is the Library's finite Galois reduction: splitting over a
finite Galois extension, the split case and Galois descent. It does not
follow either source's proof. This module contains no new mathematics; the
Lean proof only combines the eight published results named above.
