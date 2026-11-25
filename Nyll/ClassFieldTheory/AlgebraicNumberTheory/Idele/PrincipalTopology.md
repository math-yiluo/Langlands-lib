# The principal ideles are discrete and closed

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, this file proves that the principal ideles Kˣ form a discrete subgroup of the idele group, and hence a closed one.

## Main definitions and results

- `IdeleGroup.infiniteMixedEmbedding`: the infinite component of an idele, as a point of Mathlib's Minkowski space `mixedEmbedding.mixedSpace K`. It is continuous (`continuous_infiniteMixedEmbedding`). On the principal idele of x it is Mathlib's `mixedEmbedding K x` (`infiniteMixedEmbedding_principal`).
- `principal_infiniteMixedEmbedding_mem_integerLattice`: suppose the principal idele of x is a unit at every finite place (it lies in `integralAtFinitePlaces`). Then x lies in 𝓞 K, so its image lies in Mathlib's integer lattice `mixedEmbedding.integerLattice K`.
- `principalSubgroupDiscreteTopology` (instance): the subgroup `principalSubgroup K` is discrete in the subspace topology.
- `principalSubgroup_isClosed`: the principal subgroup is closed. This follows from discreteness, by `Subgroup.isClosed_of_discreteTopology`.

## Proof

The integer lattice is discrete, so there is an open set U of Minkowski space whose only lattice point is the image of 1. Consider the ideles that are units at every finite place and whose infinite part lies in U. They form an open set, since the integral ideles are open (`isOpen_supportedAt` with the empty set of places). The only principal idele in this set is 1, by the lemma above and injectivity of the Minkowski embedding.

## Points to watch

- The idele group carries the library's restricted-product topology (from imported files). Discreteness is proved for the subspace topology from it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/PrincipalTopology.lean`: the Lean file is the source byte for byte (SHA-256 `6b19cb6b683cdf58b9520f4e1eebf0873a12d7f43ab51f5f4919882e6bd8fc47`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
