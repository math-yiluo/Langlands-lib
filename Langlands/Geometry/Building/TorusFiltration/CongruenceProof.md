# The congruence shift and monotonicity of minimal congruent terms

`minimalCongruentCongruence` proves `MinimalCongruentCongruenceStatement`.
For two smooth models realizing the same point group, the generic identity
extends in both directions by `IntegralModel.smoothHomExtension` via
`exists_hom_of_map_integralPoints_le`. The two extensions carry first
congruence points into each other by `Hom.map_mem_congruenceSubgroupAt`.
Writing the depth as the sum of a fractional depth and a natural number, the
proof compares the given model with `minimalCongruentModel` of that fractional
depth or its positive congruence model. It uses
`minimalCongruentPoints_add_pnat` for the integral points and
`IntegralModel.congruenceSubgroupAt_positiveCongruenceModel` for the addition
of one to the congruence level. `IntegralModel.dilatationStructure` supplies
smoothness for the positive congruence model.

`minimalCongruentPoints_antitone` applies
`minimalCongruentPoints_antitone_of_firstCongruence` to the first congruence
model of `connectedNeronModel`. The same smoothness and addition theorems,
together with `IntegralModel.integralPoints_positiveCongruenceModel`, give
the hypotheses of that comparison.

The congruence assertion is in Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Definition B.5.3 and Proposition B.10.10, printed pp. 668
and 690, PDF pp. 699 and 721. The source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
