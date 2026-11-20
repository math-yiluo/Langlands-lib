# Semisimple representations descend to the separable closure

`Langlands.GroupScheme.reductiveSemisimpleRepresentationSeparableClosure` proves
`Langlands.GroupScheme.ReductiveSemisimpleRepresentationSeparableClosureStatement.{u}`
for every universe `u`.

Let `Gs` be the base change of `G` from `k` to its supplied separable closure
`Ks`. The theorem `connectedReductiveFieldExtensionStatement` makes `Gs`
connected reductive, providing the smoothness and affineness instances.
`IsSepClosure.sep_closed k` supplies separable closedness of `Ks`.
The theorem `exists_isMaximalTorus_isSplitTorus_of_isSepClosed` gives a split
maximal torus of `Gs`, including rank zero, and `splitPinningExistence` gives
a split pinning `p` of `Gs`.

The fourth conjunct of `splitHighestWeightBaseChange` applied to `p` and the
extension `Ka` of `Ks` gives a semisimple model on `Fin m → Ks` and a
bijective intertwining matrix from its base change to the given
representation. The base changes, matrix direction and formula for
semisimplicity agree definitionally with those of the target.

This composition of Library theorems implements the route in J. S. Milne,
*Algebraic Groups* (2017), 22.7 and 22.5, printed p. 464. The source is
registered as `milne-2017-algebraic-groups` with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
