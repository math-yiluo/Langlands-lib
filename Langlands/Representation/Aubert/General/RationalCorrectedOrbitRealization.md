# Actual cocharacters for the corrected orbit

This internal construction by Worker 561 realizes the two standard
parabolic, Levi and radical functors used by the rational corrected-orbit
modulus target as dynamic subgroups of two cocharacters of the original
torus. The second cocharacter is conjugated forward by the actual given
normalizer point. Its centralizer equals the first centralizer on every
test scheme.

`CorrectedOrbitCocharacterRealization` records these two cocharacters,
their six subgroup-functor comparisons, and their centralizer equality.
`correctedOrbitCocharacterRealization` constructs the data from the
unchanged standard-cocharacter, connected-reductive, maximal-split-torus,
generic-cocharacter and point-normalizer-comparison hypotheses, together
with the exact whole-Levi comparison of the target.

The implementation applies `StandardCocharacterStatement` to both root
sets. `normalizerEquiv` lifts the actual point-normalizer element to a
scheme-normalizing point with the same ambient value.
`groupHom_cocharacterAut_comp` expresses its conjugation as another
cocharacter of the same torus. The three
`Dynamic.*_eq_comap_of_iso` theorems give the right subgroup-functor
comparisons. Finally
`standardLevi_eq_comap_innerIso_inv_of_point_comparison` gives equality
of the two full centralizers.

The rational-point lemmas identify the first dynamic radical with
`unipotent i ν I`, the second with the inverse-conjugation preimage of
`unipotent i ν K`, and their intersection with the literal
`CorrectedFiltration.orbitUnipotentIntersection` of the target.
The right comparison uses `SubgroupFunctor.rationalPoints_comap` and
`rationalPoints_map_innerIso_inv`.

The field and universe are arbitrary, empty root sets are allowed, and
the construction needs no target subset or minimum-length assumption.
This construction supplies no Haar identity and does not discharge
character detection on the common Levi.
