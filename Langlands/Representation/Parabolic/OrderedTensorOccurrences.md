# Actual Jacquet tensor occurrences with ordered labels

Author: Worker 1216. The bundled flattened-occurrence prerequisites are by
Worker 19.

This internal adapter specializes the actual flattened tensor extraction and
return interfaces to a supplied increasing labeling of the fine blocks. For
two block shapes `B,C` of the same rank and a refinement `S` of `C`, the
input `e` bijects pairs of an outer block and an inner block with the labels
of `B`. The order hypothesis says that `e` preserves the lexicographic order
on these pairs. The size hypothesis says that each inner block has the
rank of its prescribed fine label. There is no condition on representation
supports or on distinctness of factors.

## Label and shape identification

`BlockShape.orderedFlattenLabelEquiv B C S e` is the concrete equivalence
`(C.flattenBlockEquiv S).symm.trans e` from the standard flattened labels to
the prescribed labels. It needs neither the order nor the size hypothesis.
`orderedFlatten_length` takes finite cardinalities of this equivalence to
prove equality of block counts.

`orderedFlatten_label` uses the order hypothesis to prove that `e` is the
canonical consecutive numbering, with the displayed `Fin.cast` for the
block-count equality. The proof conjugates `e` by the canonical flattening
equivalence and that cast, obtaining a strictly increasing self-map of
`Fin (C.flatten S).length`. The two finite-order inequalities
`StrictMono.apply_le` and `StrictMono.le_apply` make this self-map the
identity. Taking values and applying `Fin.ext` gives the exact label law.
`flatten_eq_of_orderedLabels` then combines that label law with the prescribed
size identities and `BlockShape.ext_of_size`, proving `C.flatten S = B` as
actual block shapes.

Both occurrence lemmas substitute this shape equality and prove that the
remaining label map is the canonical flattening equivalence by extensionality.
The rank casts in `orderedRefinementTensorFactors` then agree definitionally
with those in `flattenedBlockTensor`; their equality proofs agree by proof
irrelevance. Thus the adapter introduces no extra isomorphism or change of
the occurrence relation.

## Actual occurrence interfaces

`exists_factorized_coarseJacquet_of_ordered` then applies actual flattened
extraction. Its output retains all coarse factors, their irreducibility,
admissibility and finite length, the actual whole-coarse occurrence, and each
actual inner tensor occurrence. The ambient object must be admissible and
of finite length, each original factor irreducible and admissible, and the
total rank positive. It does not require irreducibility of the ambient object.
`subquotient_orderedJacquet_of_coarse_factors` applies actual flattened return;
it needs only the stated actual coarse and block occurrences, together with
the label, order and size data common to this module. It requires no
irreducibility, admissibility, finite length or positive total rank.

Both lemmas use `SmoothRep.IsSubquotient` on actual smooth representations.
The field universe `uF` and carrier universe `uV` are independent; the host
can instantiate the latter with `max uF uV`. The supplied topology and upper
normalized Jacquet functors are retained. Every fine factor and coarse slot
is present in both the extraction and return conclusions.

## Provenance and dependency audit

The provenance is internal: the new mathematics is finite ordered numbering,
block-shape extensionality, and substitution in the actual flattened
occurrence interfaces. No external source is claimed to state this exact
adapter. Its three direct imports are `Parabolic.FlattenedTensorOccurrences`,
`Parabolic.OrderedRefinementTensorInduction`, and
`Group.GL.AdjacentMergeShape`, under `Langlands`.

The ordered induction module supplies the displayed rank-aware tensor
definition. The present proofs do not use its induction-transitivity theorem.
The adjacent-merge module supplies combinatorial definitions and laws; these
generic proofs impose no adjacent or triple pattern. The flattened module's
actual extraction and return are described in
[FlattenedTensorOccurrences.md](FlattenedTensorOccurrences.md), together with
its lower mathematical dependency audit. In particular, extraction uses a
composition series of the whole coarse Jacquet object, the exact actual
image filtration and refined Jacquet transitivity. Admissible tensor
factorization then supplies every coarse factor. The actual refined tensor
comparison and coordinate contraction extract the inner occurrences. Return
tensors actual injective/surjective presentations and descends the original
coarse occurrence through the exact refined functor.

At Library base `8d926c3850083c700afa54adc0d07240e27fe799`, recursive traversal
contains 395 project modules including this entry and the five bundled
Worker 19 helper modules, with 170 distinct direct external imports across
the closure. There are no unresolved project imports, changed imported
Library Lean/Markdown pairs, or missing Markdown companions. The closure
contains none of the eight excluded classification targets or their named
proof successors: analytic segment classification, multisegment exhaustion,
ordered strong-head existence, ordered quotient coverage, tempered block
uniqueness, square-integrable classification, square-integrable exhaustion,
and regular exhaustion.

The mathematical route is likewise independent of those conclusions.
The lower finite-length argument inducts on `n - C.length` using compact
coefficient quasicuspidal splitting and detection by proper refinements.
That splitting is not decomposition by global supercuspidal supports.
The coarse tensor factorization uses compact averaging, minimum fixed-space
dimension, scalar Schur, Jacobson density and multiplicity-space evaluation.
The tensor comparisons descend actual quotient projections and check
equivariance on pure tensors. Neither the ordered shape identification nor
these reused bodies use global disjoint-support decomposition, ordered
quotient coverage or multisegment classification. Their detailed arguments
are recorded in the paired extraction, factorization and tensor helper files.

Development compilation of both occurrence lemmas succeeds in approved
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. This compilation is not
independent semantic acceptance or publication.
