# Actual root points and their single Lie weight

This internal construction identifies the actual rational points of a relative
root functor with its actual adjoint Lie weight space when all higher positive
integral multiples of the character are absent from the actual root support.
The hypotheses are an arbitrary field, a smooth affine group, a split torus
acting by a given homomorphism, and a nonzero character with no higher roots.
The universe and the characteristic are unrestricted. No reductivity, root
occurrence, dimension, coordinates or chosen representative is an input to
`rootPointLieEquiv`.

The first cyclic Lie span is reindexed by positive natural multipliers.
The first term is the original weight space. Every later weight space is zero:
its character is nonzero by splitness and it is not an actual relative root
by the higher-root exclusion. This proves
`semigroupWeightSpan_eq_weightSpace_of_noHigherRoots`. The published exact
cyclic Lie image of the intrinsic root functor then gives
`tangentSubmodule_eq_weightSpace_of_noHigherRoots`.

For any supplied affine representative, `representedRootLieEquiv` identifies
its actual Lie module with the original weight space. Its underlying map is
exactly the actual differential of the representing inclusion, as recorded
by `representedRootLieEquiv_coe`.

`representedRootPointLieEquiv` uses the natural vector coordinates with the
original nonzero character weight already constructed from the actual cyclic
filtration and its trivial next term. It transports root points to points of
the representative, changes from rational-point to affine-coefficient
conventions, applies `vectorPointLieEquiv`, and applies the differential
identification above. `representedRootPointLieEquiv_apply` states this formula
on represented points. Each step is an additive equivalence. Finally,
`rootPointLieEquiv` chooses the existing smooth connected closed representative;
closedness in the affine ambient group gives its affineness. The choices are
made at the representative level, and
`rootPointLieEquiv_exists_representative` records that the resulting comparison
is the constructed point-to-differential comparison for an actual representative.

The provenance is an internal deduction from the imported actual cyclic Lie
image, natural weight-coordinate and point-to-Lie constructions. The choice
of representative and coordinates is used by the construction; this module
alone does not assert independence of representative, Galois compatibility,
restriction-fiber transitivity, fixed-field coordinates, root valuations or
apartment existence.
