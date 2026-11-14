# Generic centralizers in smooth connected affine groups

This internal supporting result reuses the published
`IsSplitTorus.dynamicCentralizer_eq_torusCentralizer` theorem from
`Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction`. The ambient group is
smooth, connected and affine over any field. The torus map need not be maximal
or monomorphic, but its source must be split. Its cocharacter is generic for
the actual adjoint roots of that map.

The imported theorem identifies the dynamic centralizer and the full torus
centralizer on every test scheme under exactly these hypotheses.
`genericCentralizerPointsEquiv` is the resulting canonical multiplicative
equivalence on each test scheme, obtained from the equality of its subgroups
of ambient points.

`Dynamic.parabolic_le_of_centralizer_le_of_unipotent_le` applies the published
dynamic decomposition on each test scheme. Its centralizer and unipotent
factors lie in the supplied subgroup, hence their product does too.
`parabolic_le_of_torusCentralizer_le_of_unipotent_le` combines the two results.
No reductivity assumption is made or inferred. The conclusions are subgroup
containments, not geometric parabolicity of the dynamic subgroup.

The provenance is derived from the imported Library arguments and their
actual Lie weights and scheme-test functors; no new literature assertion is
being attributed to an external source.
