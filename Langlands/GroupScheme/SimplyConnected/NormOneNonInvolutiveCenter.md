# Central points not fixed by inversion in actual norm-one models

These internal derived lemmas give an actual central test point distinct from its
inverse. For special-linear degree `n > 2`, the test is the spectrum of the
universal root algebra `R[X]/(X^n - 1)`. Its universal root is not killed by
`X^2 - 1`, using the published polynomial degree proof over every nontrivial base
ring. The scalar-root embedding is central and injective on all test points.

Actual group-scheme isomorphisms transport this property. A central division
norm-one presentation splits over the separable closure by the published actual
matrix chart and norm-one splitting isomorphism. The special-linear witness then
transports to the given group. No reduction of the test scheme is taken; in bad
characteristic its nonreduced structure is retained.

The entry proposition `Langlands.GroupScheme.HasCentralDivisionNormOnePresentation.GeometricCentralNonInvolutionStatement` records the precise scope of
`HasCentralDivisionNormOnePresentation.exists_geometric_central_inv_ne`: its explicit hypotheses are universally quantified in a
Prop-valued definition. The implemented theorem and proof are retained.
This unit is submitted as a statement because its mathematical entry is
a proposition, rather than a data construction.
