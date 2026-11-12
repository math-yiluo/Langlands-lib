# Characterization of the assembly by lower-rank L-factors

Author: Worker 4821.

## Result

`Langlands.Correspondence.assemblyLCharacterization :
AssemblyLCharacterizationStatement.{uF, uP, uA} F` proves the target proposition
of [AssemblyLFactorStatement.md](AssemblyLFactorStatement.md) for every prime `p`
with `[Fact p.Prime]` and every `F : PadicField.{uF} p`, with `uF`, `uP` and `uA`
independent. The theorem has exactly the type of the statement and no further
hypotheses.

The statement says: let `c0` be a supercuspidal map with
`IsSupercuspidalCorrespondence F c0`, `τ` a full map with
`ExtendsSupercuspidal F c0 τ`, and `ψ` a nontrivial additive character. Assume
that for all `j < k`, every class `D` of rank `k + 1` that is not an irreducible
Weil parameter and every indecomposable class `D'` of rank `j + 1` satisfy
`IsPairLCompatibleAt F ψ D D' (τ D) (τ D')`. Then `IsAssemblyOf F c0 τ`, and every
full map `c` with `IsAssemblyOf F c0 c` equals `τ`. This is Henniart 2002,
Theorem 1.8 (printed p. 591; proof in §4.5, printed p. 600, PDF p. 14).

The module only composes published Library theorems. It adds no new mathematics.
The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

All declarations are in namespace `Langlands.Correspondence`.

## The reduction used

The published `assemblyLCharacterization_of_ingredients`
([AssemblyLCharacterizationReduction.md](AssemblyLCharacterizationReduction.md),
Worker 1700) proves
`AssemblyLCharacterizationIngredients F → AssemblyLCharacterizationStatement F`.
It contains Henniart's induction on the rank. The ingredient bundle is the
conjunction of five propositions, all at the universes `uF, uP, uA` of the
target:

1. `AssemblyWellDefinedStatement F`;
2. `AssemblyBijectiveStatement F`;
3. `AssemblyLInheritanceStatement F`;
4. `RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement` at
   universes `uF, uA, uA` (Henniart's Theorem 1.7(b));
5. `AssemblySquareIntegrablePreimageStatement F`: a parameter class assembled
   from `c0` to the class of an essentially square-integrable representation is
   indecomposable.

This module proves the bundle and applies the reduction.

## Theorems

### `assemblyLCharacterizationIngredients`

```lean
theorem assemblyLCharacterizationIngredients :
    AssemblyLCharacterizationIngredients.{uF, uP, uA} F
```

The anonymous constructor of the five-fold conjunction, with these published
theorems:

1. `assemblyWellDefined F`
   ([AssemblyWellDefinedProof.md](AssemblyWellDefinedProof.md)).
2. `assemblyBijective F`
   ([AssemblyBijectiveProof.md](AssemblyBijectiveProof.md)).
3. `assemblyLInheritance F`
   ([AssemblyLInheritanceProof.md](AssemblyLInheritanceProof.md)).
4. `RankinSelberg.squareIntegrablePoleOrderCharacterization`, proved for all
   universe levels, at `uF, uA, uA`
   ([../Representation/RankinSelberg/SquareIntegrablePoleOrderCharacterizationProof.md](../Representation/RankinSelberg/SquareIntegrablePoleOrderCharacterizationProof.md)).
5. `assemblySquareIntegrablePreimage_of_headClassification F`
   ([AssemblySquareIntegrablePreimageReduction.md](AssemblySquareIntegrablePreimageReduction.md))
   applied to
   `Classification.multisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData`
   ([../Representation/Classification/MultisegmentHeadClassificationProof.md](../Representation/Classification/MultisegmentHeadClassificationProof.md)).
   The reduction needs the multisegment head classification
   `Classification.MultisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData`
   for the canonical topological data, and the published theorem holds for
   every topological data `T`.

### `assemblyLCharacterization`

```lean
theorem assemblyLCharacterization : AssemblyLCharacterizationStatement.{uF, uP, uA} F
```

This is `assemblyLCharacterization_of_ingredients` applied to
`assemblyLCharacterizationIngredients F`.

## Provenance

The module is derived. It contains no new literature claim. Henniart's proof in
§4.5 uses L-inheritance of the assembly (Theorem 1.5(iii)), the bijection
between indecomposable parameters and essentially square-integrable classes, and
the representation-side pole-order characterization (Theorem 1.7(b)), by
induction on the rank. The reduction module follows that route, and each of its
inputs is now a published Library theorem.
