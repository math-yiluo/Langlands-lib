# A represented unipotent split series over a perfect field

Worker 1569, generalizing the Library's algebraically closed induction.

`perfectFieldSplit_of_oneDimensional` constructs a finite represented split
series for every smooth connected affine unipotent group over a perfect field,
conditional on the Library statements for closed-subgroup unipotence and
one-dimensional classification. The final exact-target proof discharges these
inputs with their published proofs.

The induction uses the well-founded order on closed supports of smooth closed
subgroups. A trivial group has the empty series. A nontrivial unipotent group
has a nonzero additive character. Its full scheme kernel has a smooth connected
reduced identity core over the perfect field. This core is a proper closed
normal subgroup, with normality on all scheme tests, so induction supplies its
split series. The represented smooth quotient by the core is affine by the
affine quotient theorem and remains connected and unipotent. The descended
nonzero map to the additive group is quasi-finite at the identity, which forces
the quotient to have relative dimension one. The perfect-field
one-dimensional classification identifies it with a one-dimensional vector
group in the unchanged all-test sense. The core series followed by this actual
represented quotient gives the successor series.

`perfectFieldSplitSeries` chooses the resulting natural-number length together
with its full `RelativeRoot.HasSplitSeries` witness. No rational-point quotient
substitutes for a represented scheme quotient, and no subgroup stability or
maximal torus conjugacy statement is used.

This is internal reduction infrastructure derived from the Library's existing
algebraically closed induction, now using perfect-field reduced subgroups and
the rational identity section for zero-dimensional triviality. The source of
the final mathematical assertion is Milne (2017), Corollary 16.24; this module
records the implemented induction rather than a distinct source translation.
