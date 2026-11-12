# The conditional assembly theorem

This module proves the published proposition
`Langlands.Correspondence.ConditionalAssemblyStatement` (module
`Correspondence/AssemblyTheorems`):

```lean
theorem Langlands.Correspondence.conditionalAssembly :
    ConditionalAssemblyStatement.{uF, uP, uA} F
```

for every prime `p` with `[Fact p.Prime]` and every `F : PadicField.{uF} p`.
The statement says: for every supercuspidal map `c0` with
`IsSupercuspidalCorrespondence F c0`, some full map `c` satisfies
`IsAssemblyOf F c0 c`, and every full map `c` with `IsAssemblyOf F c0 c` satisfies
`IsFullCorrespondence F c`. The theorem has no further hypotheses.

## Literature

Henniart 2002 (`henniart-2002-characterization`), Theorem 1.5 (printed p.590) and
§2.9 (printed p.596): the supercuspidal bijection is extended to all
Frobenius-semisimple Weil–Deligne classes through the block decomposition and the
Langlands classification, and the extension inherits the operation and pair-factor
compatibilities.

## Implemented proof

The proof is a single application of the published reduction
`conditionalAssembly_of_fivePrerequisites` (module
`Correspondence/AssemblyConstruction`) to the published proofs of its five
premises, all at the same universes `uF, uP, uA`:

| Premise | Published proof | Module |
| --- | --- | --- |
| `AssemblyWellDefinedStatement F` | `assemblyWellDefined F` | `Correspondence/AssemblyWellDefinedProof` |
| `AssemblyBijectiveStatement F` | `assemblyBijective F` | `Correspondence/AssemblyBijectiveProof` |
| `AssemblyOperationStatement F` | `assemblyOperation F` | `Correspondence/AssemblyOperationProof` |
| `AssemblyLInheritanceStatement F` | `assemblyLInheritance F` | `Correspondence/AssemblyLInheritanceProof` |
| `AssemblyEpsilonInheritanceStatement F` | `assemblyEpsilonInheritance F` | `Correspondence/AssemblyEpsilonInheritanceProof` |

Inside that reduction:

- **Existence.** `assemblyOfWellDefined` chooses, at every rank `n` and parameter
  class `D`, the unique automorphic class assembled from `D`;
  `assemblyOfWellDefined_isAssemblyOf` shows that this choice satisfies
  `IsAssemblyOf F c0`.
- **Full correspondence.** For an assembly `c` of `c0`,
  `isFullCorrespondence_of_assembly_inheritance` takes the reciprocity candidate
  and the rank-one, determinant, twist and supercuspidal-dual compatibilities from
  the hypothesis `IsSupercuspidalCorrespondence F c0`. Rankwise bijectivity of `c`
  comes from the bijectivity premise; rank one, determinant/central character,
  quasi-character twists and smooth duals from the operation premise; pair
  L-factors from the L-inheritance premise; and pair epsilon factors, for the same
  reciprocity candidate, from the epsilon-inheritance premise.

Arbitrary monodromy and all irreducible admissible classes, nongeneric included,
are covered because the domains `WeilDeligneClass F n` and `AutomorphicClass F n`
of `FullMap F` are those of the published statement, which is unchanged.

The compiled theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
