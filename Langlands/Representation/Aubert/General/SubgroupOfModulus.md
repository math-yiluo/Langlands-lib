# Actual Haar normalization inside a closed ambient subgroup

This internal construction and its transport laws compare the actual Haar characters used by the
generic normalized parabolic functors with those used by their Levi-in-Levi
versions. It is derived from the published definitions in
`Aubert.General.Parabolic`, `HaarModulus`, and the Haar-conjugacy theorem in
`HarmonicAnalysis.HaarConjugacy`. It asserts no geometric lemma or orbit
comparison.

For subgroups `U ≤ M` of any group `G`, `subgroupOfNormalizerMap` is the group
homomorphism

`normalizer (U.subgroupOf M) →* normalizer U`

that sends an element of `M` to its underlying element of `G`. Its membership
proof uses Mathlib's `Subgroup.subgroupOf_normalizer_eq`: because every element
of `U` belongs to `M`, normalization of `U` inside `M` detects normalization
of the entire ambient `U`. This is the concrete map for comparing the two
normalizer characters, rather than a choice of unrelated normalizer elements.
`subgroupOfNormalizerMap_apply` records the underlying-element formula.
For any topology on `G`, `continuous_subgroupOfNormalizerMap` proves its
continuity in the induced subgroup topologies by composing the two subtype
projections and then lifting into the ambient normalizer subtype. The map
itself does not require topology or closedness.

Let `G` be a locally compact topological group, `M` a closed subgroup, and `U`
a closed subgroup contained in `M`. For `g` in `M` normalizing `U`, conjugation
on `U.subgroupOf M` corresponds to conjugation on `U` through the continuous
group isomorphism `subgroupOfContinuousEquiv`. Consequently
`closedNormalizerCharacter_subgroupOf` identifies their actual positive Haar
scalars. The convention is the one in `HaarModulus`: the scalar multiplies the
pushforward of Haar measure to recover the original measure.

The proof equips both copies of `U` with their Borel measurable structures and
derives their local compactness from closedness. The conjugacy square commutes
definitionally, and `Geometric.haarChar_eq_of_conjugacy` identifies the Haar
scalars. Extensionality of positive real units gives the character equality.
No comparison between arbitrary normalizing characters is an assumption.
The homomorphism equality `closedNormalizerCharacter_subgroupOf_comp` then
identifies the inside character with the ambient character composed with
`subgroupOfNormalizerMap`; its proof applies the same pointwise comparison to
each inside normalizer element.

For an acting subgroup `L` contained in `M` and normalizing `U`,
`normalizes_subgroupOf` obtains normalization inside `M` by the existing
normalizer-comap inclusion. `closedRestrictCharacter_subgroupOf` specializes
the Haar comparison to `L.subgroupOf M`. The final two lemmas unfold the
canonical positive square root and its inverse to identify the actual complex
half-modulus and inverse half-modulus through the same continuous
identification. The positive square-root choice and the direction of the
inverse are preserved.

These results hold without reductivity, a root system, a character-compatibility
condition or a representation-theoretic premise. In the rational geometric
lemma they supply only transport of normalization between the same actual
radical in two ambient groups. Both orbit Haar correction twists, modulus
balance between distinct radicals, graded-piece identifications, smooth
realization, and compact/full-induction comparisons remain separate
obligations.

The proof bodies use no geometric lemma, adjointness, cuspidal support,
character independence or Langlands classification. The import of `Parabolic`
brings the normalized functor constructions and their imported-module closure;
those representation constructions are not invoked in these proof bodies.
The namespace of the reused Haar-conjugacy theorem does not make it a
representation-theoretic geometric lemma: it is the general invariance of the
Haar scaling scalar under a continuous group isomorphism.

Author: Worker 1263.
