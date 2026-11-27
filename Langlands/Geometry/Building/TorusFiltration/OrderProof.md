# Separation and discrete jumps of the minimal congruent filtration

`minimalCongruentOrder` proves `MinimalCongruentOrderStatement`.
The decreasing property is `minimalCongruentPoints_antitone`.
For separation, `minimalCongruentPoints_pnat` identifies the positive integral
depths with the congruence levels of the connected Néron model.
`IntegralModel.integralPointMap_injective` makes the same integral section
represent a point at each level. The reductions at all positive levels
therefore agree with those of the identity, so
`IntegralModel.eq_of_reductionAt_eq` gives the identity section.

For discreteness, the smooth shallow model maps to the connected Néron model
by smooth homomorphism extension. `ConnectedGenerationField.exists_generated_points`
represents the image of its special-fibre homomorphism by a smooth connected
closed subgroup. Henselian reduction and containment of the first congruence
subgroup identify the shallow point group with the preimage of this image.
Containment of shallow point groups gives containment of their closed
reduction subgroups by `SubgroupFunctor.exists_factor_of_algClosed_points`.
`BorelExistence.isIso_of_coordinateKernel_height_le` shows that equal heights
of the defining prime ideals give equal shallow point groups. These heights
are bounded by the height of the ideal of the identity subgroup.

A jump has a strictly larger term than every term at greater depth. Two
jumps of equal integer part with equal shallow heights would have the same
term by `minimalCongruentPoints_add_pnat` and the shallow realization, so
there are finitely many jumps below each integer. Restricting to an open
initial interval isolates each jump by the discreteness of finite sets.

The order properties use the filtration conventions of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Definitions B.5.2 and B.10.2 and
the construction in Definition B.10.8 and Lemma B.10.9, printed pp. 667–668,
687 and 690, PDF pp. 698–699, 718 and 721. The source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
