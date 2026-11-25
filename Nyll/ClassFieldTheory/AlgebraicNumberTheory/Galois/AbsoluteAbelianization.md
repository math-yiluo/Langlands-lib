# Abelianized absolute Galois group and the maximal abelian extension

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an arbitrary field K, this file defines the maximal abelian extension of K inside Mathlib's `SeparableClosure K` and identifies its Galois group, as a topological group, with the topological abelianization of the absolute Galois group Gal(K^sep/K). Working in the separable closure makes the construction uniform in all characteristics.

## Definitions

- `absoluteCommutatorClosure K`: the closure of the commutator subgroup of Gal(K^sep/K), as a closed subgroup; an instance says it is normal.
- `maximalAbelianExtension K`: its fixed field in K^sep. Instances: it is Galois, and abelian Galois (`maximalAbelianExtension_isAbelianGalois`), over K.
- `absoluteAbelianizationMulEquivMaximalAbelianGalois K`: the group isomorphism from `TopologicalAbelianization Gal(K^sep/K)` to Gal(K^ab/K); by `..._mk` it sends a class to the restriction of a representative.
- `absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K`: the same map as an isomorphism of topological groups.
- `finiteAbelianExtensionEmbeddingIntoMaximalAbelianExtension K L`: for L/K finite abelian Galois, a K-embedding of L into K^ab, through an embedding of L into K^sep. `finiteAbelianExtensionInMaximalAbelianExtension` is its image, as a finite Galois intermediate field of K^ab, and `finiteAbelianExtensionEquivInMaximalAbelianExtension` identifies L with it.

## Results

- `absoluteAbelianizationMulEquivMaximalAbelianGalois_continuous`: the isomorphism is continuous.
- `absoluteTopologicalAbelianization_totallyDisconnectedSpace` (instance): the topological abelianization is totally disconnected.
- `finiteAbelianIntermediateField_le_maximalAbelianExtension`: every finite-dimensional abelian Galois intermediate field of K^sep lies in K^ab.

## Proofs

The isomorphism is Mathlib's infinite Galois correspondence for the closed normal subgroup. Continuity follows from continuity of restriction; a continuous bijection from a compact space to a Hausdorff one is a homeomorphism. Containment of finite abelian subfields holds because the commutator subgroup lies in the kernel of restriction to E, and the fixing subgroup of E is closed.

## Points to watch

- The embedding of a finite abelian extension into K^ab is a choice (`IsSepClosed.lift`); the finite layer and its identification with L are built from that embedding.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean`: the Lean file is the source byte for byte (SHA-256 `90f13ce11e9436640eef3921e94a4a047f2560e72aecf4b16dc6cbaa739e9874`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
