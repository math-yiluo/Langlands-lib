# Cohomology vanishing for quasi-split trialitarian groups

`totallyComplexQuasiSplitTrialitarianCocycleVanishing` proves
`TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement.{u}`.
For a simply connected, absolutely almost-simple, quasi-split group of
trialitarian type over a totally imaginary number field, every cocycle
on a finite Galois field cover is a coboundary on that cover.

In the cyclic case the cocycle defines a pure inner twist. When all
vertices of its Tits index are marked, the twist is quasi-split and
the proof uses vanishing in a Borel subgroup. An isotropic twist with
an unmarked vertex is handled by the simply connected derived group
and the cocenter of the centralizer of a maximal split torus. An
anisotropic twist splits over the cubic diagram field.
`trialitarianCubicSplitMaximalTorus` then builds a maximal
torus over the base split by the cubic field. It first descends a
triple intersection of leaf parabolics, then descends a regular
centralizer inside the resulting Levi. The two `A₂` coefficient
groups associated to the resulting torus and the arithmetic of
reduced norms give triviality of torus cocycles in the twist.
Reduction through that torus gives triviality of the original
cocycle. These two branches are combined in
`totallyComplexQuasiSplitCyclicTrialitarian_of_cubicSplitTorus`.

For a star action with symmetric-group image, the sign kernel
gives a quadratic extension where the diagram action is cyclic.
The cyclic result applies over that totally imaginary extension.
Triviality there and local triviality over the base give triviality on
the original cover by the quadratic Hasse kernel. The final theorem
applies `totallyComplexQuasiSplitTrialitarian_of_cubicSplitTorus` to
the constructed maximal-torus theorem.

The source of the vanishing argument is Platonov and Rapinchuk,
*Algebraic Groups and Number Theory* (1994), §6.8, printed pp. 371–373.
