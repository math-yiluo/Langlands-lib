# Functoriality of the minimal congruent filtration

`minimalCongruentFunctoriality` proves `MinimalCongruentFunctorialityStatement`.
When the integer part of the depth is zero, it applies
`map_minimalCongruentShallowSubgroup_le`. At a positive integral level it
chooses `minimalCongruentModel` at the fractional depth in each torus and
uses `minimalCongruentShallowCongruence_eq` to read the filtration as
congruence subgroups of these models. The shallow point inclusion extends the
generic homomorphism by `exists_hom_of_map_integralPoints_le` and
`IntegralModel.smoothHomExtension`. `Hom.map_mem_congruenceSubgroupAt`
then carries the source congruence subgroup into the target at the same level.

This proves the functoriality assertion of Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Proposition B.10.10, printed p. 690, PDF p. 721.
The source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
