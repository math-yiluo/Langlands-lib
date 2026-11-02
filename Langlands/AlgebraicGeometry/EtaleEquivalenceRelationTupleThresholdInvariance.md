# Invariance of symmetric tuple threshold opens

This internal helper derives compatibility of the symmetric charts with the
threshold filtration used in Stacks Lemma 68.8.3, Tag 0BBN, first and second
proof paragraphs. The source is registered as
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`,
file `0BBN.txt`. The source constructs the free symmetric quotients of distinct
tuples and defines thresholds by the existence of sufficiently many distinct
geometric coordinates. The results here are derived from the preceding actual
scheme quotients, their effective kernel pairs, and the already proved
invariance of the original object thresholds. Index `n` means `n + 1`
coordinates throughout.

Let `E` be an étale equivalence relation in an arbitrary universe `u`, with
separated source map. `tuplePermutationRelationMap n` maps the disjoint union
presenting its permutation action to the original relation scheme. On the
component labelled by a permutation `g`, it is the relation arrow from
coordinate zero to coordinate `g 0`. The `_t` and `_s` equations identify its
target and source with the zeroth coordinate after and before the action.
These constructions allow the permutation to vary across components.

All remaining declarations assume that both the object and relation schemes
of `E` are affine; they require no closed-joint-endpoint assumption.
`tupleSymmetricMap_pointRel_of_eq` uses the effective kernel-pair square of
the finite étale quotient to lift two ordered points with equal quotient image
to a point of the action relation. Its image under
`tuplePermutationRelationMap` witnesses that their zeroth coordinates are
related in the original relation.

`tupleSymmetricMap_mem_threshold_iff` says that a quotient image belongs to
the symmetric threshold exactly when the ordered representative's zeroth
coordinate belongs to the original threshold. The reverse direction is the
defining image witness. For the forward direction, the chosen image witness
and the given representative have equal quotient image, so invariance of the
object threshold transfers membership between their zeroth coordinates.
`tupleSymmetricThresholdOpen_preimage` states this as an equality of open
subsets on the ordered distinct-tuple scheme.

`tupleSymmetricCross_threshold_iff` says that the two endpoints of any
symmetric cross arrow belong to the same threshold, even for charts of
different lengths. Surjectivity lifts the point to the ordered cross scheme.
The endpoint equations and the preceding membership criterion reduce the
claim to original object thresholds at the two zeroth coordinates. The
ordered cross arrow's actual original relation point relates those
coordinates, and invariance gives the equivalence.
`tupleSymmetricCross_threshold_preimage_eq` is the corresponding equality of
inverse-image opens.

`tupleSymmetricZeroIso_threshold_preimage` identifies the symmetric thresholds
on the one-entry chart with the original object thresholds under the
previously constructed isomorphism to `E.U`. It follows by lifting points to
ordered representatives and using that isomorphism's projection formula.
`tupleSymmetricScheme_isEmpty` proves that chart indices at least the uniform
tuple-length bound have empty underlying point types: their ordered covers
are empty and the quotient maps are surjective.

These are filtration compatibility and finiteness results. They do not
construct a Noetherian first level.
