# Coefficient restriction of the actual rational normalized induced family

This internal adapter restricts the existing universal rational normalized induced
action from its full regular coefficient algebra to complex scalars on the same
actual function carrier. The complex scalar action is restriction along the
constant inclusion. The complete rational norm family and the independent field
and inducing-carrier universes are retained. The supplied semidirect decomposition
and unipotent closedness are those of the existing normalized model; no existence
assertion is added.

The local structural instances spell out the existing additive group and regular
coefficient action on the full smooth induced functions. The complex module is
`Module.compHom` along the constant inclusion, and its scalar-tower law is the
corresponding restriction law. `inducedComplexRepresentation` applies the existing
`CoefficientRestriction.complexRepresentation` with these instances explicitly.
Its operators are the existing right translations, so smoothness is unchanged.
The compatible-coefficient instance uses regular linearity of each actual group
operator.

`inducedEvaluationIntertwiner` is the published function-value evaluation on this
same carrier, now bundled as a complex intertwiner. Additivity is its existing
additivity. For complex linearity, the semilinear evaluation law is applied to a
constant regular coefficient; evaluation fixes that coefficient. The published
right-translation law proves equivariance. The final regular-scalar theorem is
the original semilinear law for every actual regular coefficient, not just the
constants.

This is a derived actual-object adapter of the published normalized models,
coefficient restriction and evaluation laws. It does not assert full
scalar-specialization bijectivity, compact-fixed specialization bijectivity,
family finiteness, or a uniform compression exponent. Those assertions remain
separate obligations in the host stabilization proof.
