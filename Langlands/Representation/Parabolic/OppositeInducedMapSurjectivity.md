# Surjectivity of normalized opposite-parabolic induction maps

This internal derived result specializes
`Induction.smoothInductionSurjectivity` to the actual lower block parabolic
of a p-adic general linear group. It uses the published closedness of that
parabolic and compact open subgroups cofinal among open subgroups. Inflation
along the opposite Levi projection and twisting by the opposite half
modulus preserve smoothness.

The source and target complex modules have independent universes. They have
no topology. The theorem assumes smoothness of both Levi representations
and surjectivity of their specified intertwiner; it proves surjectivity of
the published `normalizedOppositeParabolicInducedMap`. This is the opposite
parabolic counterpart of `Classification.normalizedParabolicMap_surjective`,
with its independent module universes retained explicitly.
