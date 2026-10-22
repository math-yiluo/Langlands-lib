# Compact detection and exactness of smooth complex coinvariants

`Langlands.smoothCoinvariantExactness` proves exactly the existing
`Langlands.SmoothCoinvariantExactnessStatement` in `ExactStatement`.
It retains the independent group and three module universes and all original
hypotheses. The group is a topological group in which every finite subset is
contained in a compact open subgroup. The modules are arbitrary complex
modules, with no topology on them. Only the middle representation in the
exactness clause is assumed smooth. No local compactness, separation,
admissibility, dimension, or length assumption is added.

## Implemented proof

`coinvariants_mem_ker_iff_compact` uses Mathlib's finite-subset characterization
of membership in a span. Choose a group element and vector realizing each of
finitely many generating relations, and apply finite containment to those group
elements. Every chosen relation belongs to the compact subgroup's relation
span, and hence so does the original vector. The converse is the elementary
inclusion `coinvariants_ker_comp_subgroup_le`. This argument does not require
smoothness or the topological-group compatibility instance; the main statement
retains its original smoothness hypothesis.

`Compact.orbitMean_apply` proves that translating the initial vector leaves
its orbit set unchanged, so leaves its orbit mean unchanged.
`Compact.mk_orbitMean` shows that the mean of a finite orbit has the same
coinvariant class as its initial vector: all summands have that class, and the
nonzero finite orbit cardinal cancels its inverse over the complex numbers.
These two identities show that the kernel of the existing compact averaging
map is precisely the subgroup relation span in
`Compact.averageMap_eq_zero_iff`. One inclusion follows from the mean identity
on coinvariant classes; the other follows by checking the relation generators
and extending to their span by linearity.

`coinvariants_map_injective_of_smooth` is the reusable left-exactness helper.
It takes finite containment, an intertwiner `i`, injectivity of `i`, and
smoothness of its target. It concludes injectivity of Mathlib's
`Representation.Coinvariants.map` without a short exact sequence premise.
Source smoothness follows from the published smoothness-transfer theorem.
If the image of a representative is a relation, compact detection finds a
compact open subgroup where its average vanishes. Naturality of the published
averaging map and injectivity of `i` imply that the source average vanishes.
The averaging-kernel characterization makes the source representative a
relation too. The linear map therefore has zero kernel and is injective.

`coinvariants_ker_map_of_surjective` proves that a surjective intertwiner maps
the source relation submodule onto the target relation submodule. It checks
the generators in both directions and uses surjectivity to lift their vectors.
`coinvariants_map_range_eq_ker` then proves algebraic middle exactness: if the
image of `v` is a relation, lift that relation to a source relation `z` with the
same image. The difference `v - z` lies in the original kernel and hence in the
original image. Its coinvariant class equals that of `v`.
`coinvariants_map_surjective` lifts quotient representatives directly.
These three algebraic helpers require neither topology nor smoothness.
The closing theorem assembles compact detection and the three induced-map
conclusions, using the actual Mathlib quotient objects and maps throughout.

## Provenance and dependencies

The mathematical source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019, pp.3–4: the relation-span
definition, Lemma III.3.3(a)–(c), and Proposition III.3.4 with its proof.
The registered source is `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Worker 200 read the retained original pp.3–4. Neither the workspace Library
nor the project notes had an `errata` directory at this workspace base.
The original has incomplete cross-references in the proof of III.3.3 and the
averaging discussion in III.3.4; the present proof explicitly supplies those
finite-span and averaging arguments using the accepted Library definitions.

The abstract finite-containment scope is the derived formulation already fixed
by the target. The proof does not establish the separate p-adic geometric
containment result. Normalized finite orbit sums implement averaging without
introducing an integral on an unspecified module topology.

Project imports are the unchanged `Jacquet.ExactStatement`,
`Compact.ProjectionProof` (including the compact averaging definitions and
finite mean lemmas), and `Smooth.Transfer.SubquotientProof`. Published results
are reused by their Lean names. The original statement pair and its full import
closure are unchanged. This new pair is authored by Worker 200.
