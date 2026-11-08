# Recognizing Borel overgroups from their actual root support

This internal definition and its supporting lemmas express an actual-root
support presentation and prove that it recognizes a smooth Borel overgroup as
the corresponding dynamic parabolic on every test scheme. They do not
construct a cocharacter or prove that an arbitrary Borel overgroup has such a
root-support presentation.

The proposition
`Langlands.GroupScheme.AbsoluteBorelOvergroup.HasNonnegativeRootSupport j F ζ`
means that, for every actual nonzero root of `j`, occurrence in the intrinsic
tangent support of `F` under conjugation by `j` is equivalent to nonnegative
pairing with the specified integral cocharacter `ζ`. The definition assumes
an arbitrary field, an affine ambient group scheme, a commutative group scheme
mapping to it, and an all-test subgroup functor. It asserts neither smoothness
nor existence of `ζ`; it tests only actual roots and makes no assertion about
the zero weight. The recognition lemmas supply the separate zero-weight
argument under their maximal-torus and containment hypotheses.

The main theorem is
`Langlands.GroupScheme.borelOvergroup_eq_dynamicParabolic_of_rootSupport`.
Its hypotheses are those of the absolute Borel-overgroup cocharacter task,
together with a supplied integral cocharacter of the specified split torus and,
for every actual root, equivalence between occurrence in the overgroup's
intrinsic tangent support and nonnegative pairing with that cocharacter.
There is no connectedness premise on the overgroup.

The proof derives connectedness from the actual Borel factorization using
`borelContainingSubgroupConnectedStatement`. The torus factors through the
overgroup, so the overgroup is stable under torus conjugation. Each root
weight space is a line by the proved `splitRootLieLine`; consequently a
nonzero intersection with its tangent image contains the whole line.
The zero weight space is the tangent of the torus centralizer by the proved
Lie comparison. The proved `maximalTorusCentralizer` identifies that
centralizer with the specified maximal torus, which the overgroup contains.

The split-torus decomposition of a represented stable subgroup then identifies
the entire tangent image with the nonnegative weight span. The proved
`le_dynamicParabolic_of_tangentSubmodule_le` gives subgroup containment.
The dynamic parabolic is smooth and connected by `dynamicSmooth` and
`dynamicConnected`, and its Lie image is exactly that span by `dynamicLie`.
The proved included-subgroup full-Lie comparison
`IsSmoothConnectedClosed.eq_of_le_of_hasLieImage` gives equality.

The supporting lemmas retain their stated scope over an arbitrary field:
the zero-weight containment, the saturation of a root Lie line, the exact
nonnegative tangent image, and the dynamic comparison for a smooth connected
closed subgroup containing the torus. The Borel wrapper uses an algebraically
closed field only to derive connectedness.

All structural inputs are proved Library theorems with their hypotheses
discharged. No split-parabolic cocharacter classification, rational Bruhat
classification, or parabolic-intersection result is used. The provenance of
this module is the internal combination just described; it proves the
recognition step only, leaving the substantive existence of the root-support
presentation explicit. It applies in all characteristics and does not require
nonempty roots or positive rank.

The root-line containment lemma `weightSpace_le_tangentSubmodule_of_mem_support` is shared with `BorelOvergroupRankOne`. Its proof uses the same one-dimensional root space and a nonzero vector in the tangent image.
