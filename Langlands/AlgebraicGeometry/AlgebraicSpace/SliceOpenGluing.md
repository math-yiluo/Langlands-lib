# Slice open-chart gluing

Worker 336 adapts actual scheme gluing to an arbitrary fixed base `S` and the
lifted Yoneda value universe of Basic. The concluding theorem
`SliceOpenGluing.exists_representation` states that a family indexed by `I : Type u`
of relatively representable open chart maps into an actual fppf sheaf on `Over S`,
whose coproduct is locally surjective for `fppfTopology S`, supplies an actual
`V : Over S` and a natural isomorphism `(schemeYoneda S).obj V ≅ G.obj`.
There are no affineness, finiteness, separation, or prior representation hypotheses.
The theorem uses the published `IsOpenImmersion` predicate from
`SchemeLocalGeometry`. Its internal `openProperty` is the underlying inverse image
of scheme open immersions along `Over.forget S`, used to build the overlaps.
The entry module `OpenChartGluingProof` applies this construction to prove the
published `OpenChartGluingStatement`.

The proof first shows that relative monomorphisms remain monomorphisms for lifted
Yoneda. Represented pairwise overlaps and the generic symmetry and triple-pullback
identities form `sliceData : CategoryTheory.GlueData (Over S)`. Forgetting the base
gives actual `Scheme.GlueData`, so Mathlib constructs a glued scheme. Its chart
structure maps descend through the multicoequalizer; `structureMap` and `glued`
therefore retain an actual morphism to the original base.

The charts and represented overlaps form a pre-hypercover in `Over S`. Its covering
conditions follow from Mathlib's scheme-gluing Zariski hypercover, the inclusion
of the Zariski topology in the fppf topology, and the sieve equivalences defining
the topology on a slice. The actual fppf sheaf condition then glues compatible
chart sections by `OneHypercover.isLimitMultifork`. Lifted Yoneda converts the
glued section into `yonedaGluedToSheaf`, whose restriction to every chart is the
original map. Factorization of the coproduct of the charts proves local
surjectivity. For local injectivity, pull back the chart cover along two maps to
the glued scheme, intersect those covering sieves, and compare their local chart
factorizations. Equality of the sheaf sections gives a map into the represented
overlap; the scheme gluing condition identifies the two maps to the gluing.
Mathlib's local-bijection criterion for sheaves gives the isomorphism, and
forgetting its sheaf structure gives the stated natural presheaf isomorphism.

The mathematical criterion motivating this construction is Stacks Project Lemma
26.15.4, Tag 01JJ, registered as
`stacks-open-chart-representability-2026-11-01`, directory SHA-256
`51771f7545361ce0b0f4f3ebe79f53f862d299ecc08344f3273aeb9a8dc84201`,
retained at `/home/taskhub/pilot/literature/Stacks Project - Open chart representability (HTML snapshot 2026-11-01)`.
The original lemma and proof were read in full in the preceding conversation.
The present slice, fppf, and lifted-value formulation and its explicit descent of
the structure map are internal derived content. The Lean proof follows actual
scheme gluing and a sheaf comparison, with no reduction to a smaller-value sheaf.

The lifted-Yoneda helpers and comparison argument adapt the retained
Anthropic/NYLL implementation registered as
`external-lean-reuse-snapshots-2026-10-21`, file
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/SchemeTheory/LocalGeometry/LocalRepresentabilityULift.lean`,
NYLL snapshot commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The file was read in full again during this implementation. Its original
Anthropic, Mathlib, and Naganori Yamaguchi notices and attribution links are
preserved in the Lean header. The registered directory SHA-256 is
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
confirmed against the source entry in the published external reuse survey. The generic scheme and hypercover constructions
also use the prepared Mathlib sources `AlgebraicGeometry/Sites/Representability`,
`AlgebraicGeometry/GluingOneHypercover`, `CategoryTheory/GlueData`, and
`CategoryTheory/Sites/Over`.

The actual scheme construction and sheaf comparison have been compiled in the
prepared environment at arbitrary universe `u`, with only `propext`,
`Classical.choice` and `Quot.sound`. Development compilation supplies no
independent semantic acceptance or publication. Worker 133 contributed to the
interface and the parent proof decomposition; the implementation and the
slice adaptation are by Worker 336.
