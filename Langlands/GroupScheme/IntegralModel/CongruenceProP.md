# The actual local-field congruence subgroups are pro-p

This internal result applies the actual congruence-power bounds to the published
congruence neighborhood basis. Let `F` be a nonarchimedean local field in any
universe `u`, let `G` be an affine group scheme over `F`, and let
`M : IntegralModel ↥𝒪[F] F G`. No smoothness assumption is needed.

`localFieldCongruenceOpenSubgroup M n` bundles the existing subgroup
`M.congruenceSubgroupAt n` as an open subgroup of the original generic
rational-point group with its canonical point topology. The underlying subgroup
is unchanged.

`localField_isPGroup_congruenceQuotient M n N` proves that every element of the
quotient of that subgroup by any open normal subgroup `N` is killed by a power
of `ringChar 𝓀[F]`. The image of `N` is an open identity neighborhood in the
ambient group, because the level-`n` congruence subgroup is open. Cofinality
therefore puts some level `k` inside that image. The congruence-power bound puts
`x ^ (p ^ k)` in level `n + k`, hence in level `k`, where `p` is the actual
residue characteristic. This gives the required quotient identity.

`localField_isProP_congruenceSubgroupAt` combines this result with the published
compactness of the same congruence subgroups, total disconnectedness of affine
rational points over a nonarchimedean local field, and primality of the
characteristic of the finite residue field. It proves `IsProPSubgroup` with the
original induced topology. `localField_isProP_congruenceSubgroup` specializes
to the published level-one subgroup using its existing equality with level one
of the tower.

The provenance is internal. The proof uses `CongruencePowers`,
`CongruenceNeighborhoodBasisProof`, and the rational-point evaluation embedding.
This unit proves the pro-p property of the congruence kernel; the pro-p property
of a larger radical preimage also needs control of its special-fibre image.
