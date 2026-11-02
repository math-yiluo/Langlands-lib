# Proof of Renard III.1.4 irreducible existence

Implementation and explanation: Worker 1210, adapting the cyclic proof route
of Worker 379 and the finite-generation/coatomicity argument of Worker 238.

`Langlands.SmoothRep.renardIrreducibleExistence` proves exactly the published
`Langlands.SmoothRep.RenardIrreducibleExistenceStatement.{uK,uG,uV}`.
For every field `k`, topological group `G` and nontrivial actual smooth `A`,
it gives an irreducible subquotient; source categorical finite type gives an
irreducible quotient; source categorical finite composition length gives an
irreducible subrepresentation. The field, group and carrier universes are
independent, and every witness retains the original carrier universe.
`IsTopologicalGroup G` remains quantified inside the target proposition.

## Actual categorical comparisons

The helper declarations are in
`Langlands.SmoothRep.RenardIrreducibleExistence`.

`not_isZero` proves that a nontrivial carrier is a nonzero object: if the
identity morphism equals zero, evaluating at a nonzero vector is a contradiction.

`isIrreducible_of_simple` proves that categorical simplicity implies
irreducibility of the actual invariant-submodule lattice. Equality of bottom
and top would force the identity to vanish. For each invariant submodule its
actual subtype morphism is monic by the published
`SmoothRep.mono_iff_injective`. If that morphism is zero, the submodule is
bottom. Otherwise categorical simplicity makes it an isomorphism; the published
`SmoothRep.epi_iff_surjective` then makes the submodule top.

These comparisons are proved for the actual smooth category. The finite-type
and finite-length arguments retain the source categorical predicates directly.

## Unrestricted subquotient

`exists_irreducible_subquotient` follows the cyclic route of Worker 379's
[`Category/IrreducibleSubquotientExistence`](../Category/IrreducibleSubquotientExistence.md),
now over an arbitrary field. Choose `v ≠ 0` and let `N` be its span as a
`k[G]`-module, using `Representation.asModuleEquiv` to place the vector in the
actual group-algebra module. `Subrepresentation.ofSubmodule' N` is an invariant
submodule `S` of `A`, containing `v`. Its smooth subrepresentation `B` is
therefore nontrivial.

An explicit bijective `k[G]`-linear map identifies `B.representation.asModule`
with `N`: it is the actual subtype intertwiner, converted to a module map and
corestricted to `N`. A singleton span is finitely generated
(`Module.Finite.span_of_finite`), so this equivalence makes `B`'s group-algebra
module finitely generated. Mathlib's coatomic submodule lattice, transported by
`Subrepresentation.subrepresentationSubmoduleOrderIso`, gives a maximal proper
subrepresentation `T`. This adapts the finite-generation/coatomicity argument
of Worker 238's
[`QuasicuspidalEmbedding.exists_isCoatom_subrepresentation`](../CuspidalSupport/QuasicuspidalEmbeddingProof.md).

`quotient_isIrreducible_of_isCoatom` proves that the actual smooth quotient
`B/T` is irreducible. It converts the surjective quotient intertwiner to a
`k[G]`-linear map, identifies its kernel with `T.asSubmodule`, and transports
the coatom property through the same order isomorphism.
`isSimpleModule_iff_isCoatom` makes the kernel quotient simple, and
`LinearMap.quotKerEquivOfSurjective` transports simplicity to the actual smooth
quotient's group-algebra module. Mathlib's
`Representation.irreducible_iff_isSimpleModule_asModule` finishes.
The identity isomorphism then witnesses `IsSubquotient (B/T) A`.

All spans, subtypes and quotients have the original carrier universe.
Finite generation is established only for this constructed cyclic module;
this clause requires no finiteness hypothesis on `A`.

## Source categorical finite type and finite length

`exists_irreducible_quotient_of_finiteType` applies the published categorical
`Langlands.Renard.exists_simple_cokernel_of_finiteType` to `not_isZero A` and
the given `Langlands.Renard.IsFiniteTypeObject A`. It obtains a subobject whose
cokernel `B` is simple. `isIrreducible_of_simple` makes `B` irreducible, and
the cokernel projection is an epimorphism, hence an actual surjective
intertwiner by `epi_iff_surjective`. That projection witnesses `IsQuotient B A`.
This uses no comparison between categorical finite type and group-algebra
finite generation.

`exists_irreducible_subrepresentation_of_finiteLength` uses the given
categorical composition chain from `Langlands.Renard.IsFiniteLength A`.
Its length is positive: a length-zero chain makes `A` a zero object,
contradicting `not_isZero A`. The first successive cokernel is simple.
`Langlands.Renard.simple_cokernel_ofLE_iff_covBy` makes its adjacent subobjects
a cover; the first is bottom, so the next is an atom. The categorical
`subobject_simple_iff_isAtom` makes that actual subobject simple, and
`isIrreducible_of_simple` makes it irreducible. Its subobject arrow is monic
and therefore an actual injective intertwiner by `mono_iff_injective`,
witnessing `IsSubrepresentation`.

The final theorem assembles these three results. No Grothendieck, AB6,
Hecke-equivalence, admissibility, finite-dimensionality, countability or extra
coefficient premise is used. The Hecke equivalence and other Chapter III
assertions remain outside this proof.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages, read in that edition, are III.1.4's final paragraph
(printed p.60 / PDF66), A.I.2–A.I.3 (printed pp.248–249 / PDF254–255), and
A.VI.3 (printed pp.263–264 / PDF269–270). These support the three existence
assertions and the categorical finiteness conventions; the implemented proof
uses the algebraic cyclic construction and the categorical results described
above.

The explicit nonzero qualification and arbitrary-field/topological-group
generality are exactly those documented in the
[published statement](RenardIrreducibleExistenceStatement.md). The printed
III.1.4 summary leaves nonzeroness implicit; zero is a counterexample to its
unqualified form. A.VI.3 defines simple objects to be nonzero and assumes a
nonzero object in its finite-type simple-quotient proposition.
The retained statement's source corrections, including nonempty chains in the
finite-type predicate and the composition-factor index range, are unchanged.

The supplementary author errata for the 2010 edition, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF2–3 and PDF18–19. The appendix's chain-based Zorn correction is
respected by the imported categorical theorem. The 2026 edition remains
governing. Related source discrepancies are recorded in
[`notes/renard/appendix-a-corrections.md`](../../../notes/renard/appendix-a-corrections.md).

The local helpers are derived comparison and existence results, with their
implemented arguments given above; they introduce no axioms. Published
category and lattice results are imported by Lean name. Prepared environment:
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
