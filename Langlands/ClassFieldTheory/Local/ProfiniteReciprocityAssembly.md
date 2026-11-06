# Assembly from geometric finite Artin systems

Author: Worker 1651.

This internal structural construction connects the published finite-system
statement with the unchanged profinite reciprocity statement. It derives no
arithmetic existence theorem.

`ProfiniteReciprocityAssembly.geometricFamilyEquiv` is an equivalence between
the subtype of continuous homomorphisms satisfying
`GeometricProfiniteReciprocityRelation F T` and the subtype of finite families
satisfying `GeometricFiniteArtinSystemRelation F T`. It applies to every prime,
every p-adic field `F : PadicField.{u} p` in an arbitrary universe, and every
supplied original datum `T : F.TopologicalData`. The topology is exactly
`T.topology`. Characteristic zero, and hence perfectness for reconstruction,
follows from the field's algebra structure over `Padic p`.

The forward map takes every actual finite field restriction of the supplied
continuous homomorphism. Its finite system and geometric residue congruence
are the corresponding conjuncts of the given profinite relation. The inverse
reconstructs from the same finite family's restriction certificate and uses
`reconstruct_geometric` to recover the entire profinite relation. Recovery of
every finite component proves the right inverse; injectivity of finite
restriction proves the left inverse. Equality in both subtypes is equality of
their underlying maps or dependent families.

`profiniteReciprocity_of_finiteArtin` proves the implication

```lean
GeometricFiniteArtinSystemExistenceUniqueness.{u} →
  ProfiniteReciprocityExistenceUniqueness.{u}
```

The proof introduces every quantified prime, field and supplied datum. It
reconstructs from the unique finite family supplied by the premise.
`reconstruct_geometric` proves the full profinite relation, including density,
all exact norm kernels, surjectivity of all finite restrictions, every
restriction identity, and the original residue congruence. For any competing
profinite map, its finite family satisfies the same geometric finite relation.
Finite-family uniqueness identifies it with the chosen family. Component
recovery and injectivity of finite restriction then identify the two profinite
maps.

Both relations retain every actual finite abelian extension, every supplied
extension datum, every base unit of order one, and every integral extension
element. The inverse finite automorphism and exponent
`T.residueCardinality` are exactly those in the existing statements.

Provenance is internal: this pair assembles the existing predicates using
finite-family reconstruction, recovery and separation. It changes no target
or imported pair and makes no new literature assertion. The finite arithmetic
existence and uniqueness proposition remains an explicit premise of the
implication. Its unconditional proof and the final unconditional profinite
proof are still required.
