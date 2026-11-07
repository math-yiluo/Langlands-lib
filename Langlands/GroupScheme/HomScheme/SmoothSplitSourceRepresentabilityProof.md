# Smooth representability of actual Hom from a split torus

Authors: Worker 362 and Worker 1656.

`Langlands.GroupScheme.HomScheme.smoothSplitSourceRepresentability.{u}`
proves the existing Library proposition
`SmoothSplitSourceRepresentabilityStatement.{u}`. For every scheme `S`,
split torus `H/S`, and smooth affine group scheme `G/S`, it supplies an
actual scheme `M/S` and an actual homomorphism `H_M ⟶ G_M` whose evaluation
is bijective on every test scheme over `S`, with `M → S` smooth.
The universe `u` is arbitrary. The base may be nonreduced or nonnoetherian,
and the fibres of `G` may be disconnected.

## Implemented proof

The Lean proof applies
`smoothSplitSourceRepresentability_of_torusSubgroupModuli` from
`GraphLocusUniversal` to the proved theorem
`TorusSubgroupModuli.smoothTorusSubgroupRepresentability` from
`SmoothTorusSubgroupRepresentabilityProof`, in the same universe `u`.
The subgroup-moduli premise is thereby discharged by its published proof.
The final theorem has exactly the named proposition as its type.

The imported construction works as follows. Since `H` is a split torus,
it is smooth and affine. Thus `H ×_S G` is smooth and affine. The
subgroup-moduli theorem supplies a smooth scheme `P/S` with a universal
family of actual closed relative-torus subgroups of this product. Its
own proof constructs torus charts, reduces from finite-type affine bases
to arbitrary bases, and glues the charts and their families.

The scheme `M` is `graphLocus j`, the open subscheme of `P` where the
family's first projection to `H` is invertible. The open isomorphism
locus uses the actual relative-torus source and split-torus target.
Inverting this projection and composing with the second projection
constructs `graphLocusHom j : RelativeHom H G M`.

For every `T : Over S`, evaluation of this homomorphism and then taking
its graph agrees with evaluation of the original subgroup family at
the composite parameter `T → M → P`. Equal evaluated homomorphisms
therefore give equal parameters by subgroup universality and
monomorphy of the open inclusion. Conversely, the graph of any actual
homomorphism `H_T ⟶ G_T` is an admissible closed torus subgroup.
Subgroup universality gives a parameter in `P`; the all-test
isomorphism-locus criterion factors it through `M`. Graph recovery then
identifies its evaluation with the original homomorphism. These are
the injectivity and surjectivity of the unchanged `HomScheme.IsUniversal`
predicate, including its actual pullback-composition comparisons.

Finally, `M → S` is smooth because it is an open immersion followed by
the smooth morphism `P → S`.

## Provenance

This module is an internal composition of the two imported Library
theorems and their implemented constructions. Their Markdown companions
describe the graph-locus and subgroup-chart proofs in detail. It adds
the unconditional conclusion by supplying the proved subgroup-moduli
input. The conclusion retains the target's scope: smooth
representability on all test schemes, without an affineness or
quasi-compactness assertion for the representing scheme.
