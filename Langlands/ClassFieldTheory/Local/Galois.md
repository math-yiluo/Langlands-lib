# Actual Galois groups and continuous abelianization

Author: Worker 21.

This construction uses Mathlib's actual algebraic closure, absolute Galois
group, finite Galois intermediate fields, and topological abelianization.
It supplies no Artin map and assumes no reciprocity theorem.

The continuous projection is the actual quotient by the closure of the
commutator subgroup. Continuous homomorphisms to a T1 commutative group kill
that closure because their kernels are closed. The resulting quotient lift
and its inverse by precomposition form `abelianizationLiftEquiv`.
`abelianizationMap` applies this construction to the composite with a target
quotient projection. The quotient's Hausdorff certificate comes from the
closedness of the subgroup.

`FiniteAbelianExtension K` is a subtype of Mathlib's existing finite Galois
intermediate fields in `AlgebraicClosure K`, with a commutativity predicate on
the actual automorphism group. It is not an independently supplied abstract
Galois group. Its restrictions use the existing normal restriction map and
its proved continuity. `abelianRestriction` is its quotient descent. The
Krull topology on this finite group is the existing discrete topology.
`fixingOpenSubgroup` packages its pointwise stabilizer as an actual open subgroup.
`finiteGroup` packages the same automorphism group as a `FiniteGrp`.
`restrictionOfLE` gives the continuous restriction for an inclusion of two
finite abelian intermediate fields. It uses their actual inclusion and the
normality of the smaller extension, not an arbitrary map between finite groups.

For a perfect field, `absoluteAbelianizationProfinite` packages the actual
quotient as a profinite group. Its compactness follows from the existing
compactness of the Galois group of the algebraic closure. Its
nonarchimedean structure follows by taking the image of an open subgroup
under the open quotient map. Closedness of the commutator closure gives
Hausdorffness, and the nonarchimedean basis gives total disconnectedness.
The local specialization takes the accepted actual finite p-adic field,
which has characteristic zero. No supplied local-field topology is needed
for the Krull topology.

`absoluteAbelianizationMap` goes from the extension's abelianized absolute
Galois group to the base's, using explicitly compatible algebraic-closure
embeddings. Independence of those choices is not asserted here.

The three topology certificates `abelianizationHausdorff`,
`quotientNonarchimedean`, and `absoluteGaloisNonarchimedean` are proved within
the module because they are intrinsic to the continuous quotient maps and
the `ProfiniteGrp` constructor. They assume no project theorem.
All group and field universes remain independent where they occur together.
The local specialization covers each prime and actual finite p-adic extension.

This module does not identify the compact profinite quotient with the
noncompact multiplicative group of the local field. The Weil quotient,
its comparison with the profinite quotient, finite-level reciprocity
relations, transfer, and the existence of normalized reciprocity remain
separate work.

## Provenance

The constructions implement the actual finite Galois groups and profinite
abelian quotient used in Serre, *Local Fields*, English edition (1979),
Chapter XI, Section 3, printed pages 169–171 (PDF pages 175–177), and
Sections 4–5, printed pages 172–175 (PDF pages 178–181).
Only the underlying objects and ordinary quotient constructions are used;
none of that source's local class-field-theory assertions is assumed.
Registered source: `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The implementation derives its intrinsic certificates from pinned Mathlib:
`FieldTheory/AbsoluteGaloisGroup.lean`,
`FieldTheory/Galois/GaloisClosure.lean`,
`FieldTheory/Galois/Profinite.lean`,
`GroupTheory/Abelianization/Defs.lean`,
`Topology/Algebra/Group/TopologicalAbelianization.lean`,
`Topology/Algebra/Group/Quotient.lean`, and
`Topology/Algebra/Nonarchimedean/TotallyDisconnected.lean`.
The sole project dependency is accepted `Langlands.LocalField.Definitions`,
artifact `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` version 1.
Its effective Lean SHA256 is
`8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`.
Its current availability was verified at Library commit
`9007729971e6e6ecea63b5567b6d1621769ccfb0`, with no missing or changed files
or unavailable dependencies.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation checks intrinsic construction certificates; independent semantic
review and publication are still required.

## Topic-hierarchy migration

Worker 63 relocated this pair from `Langlands.LocalClassField.Galois` to
`Langlands.ClassFieldTheory.Local.Galois` at Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 remains the
author of every mathematical declaration and construction certificate above.
Only imports were rewritten in the Lean source; all declaration text, including
universes, hypotheses, definitions, proofs and instance declarations, was retained.
The old path is a declaration-free re-export with its own paired documentation.

The full [module table and declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger)
records this mechanical migration and its validation. Original source citations
and mathematical explanations are retained; their historical submission-status
remarks describe the original contribution, not this relocation's review status.
