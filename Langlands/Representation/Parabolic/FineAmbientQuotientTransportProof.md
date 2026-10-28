# Fine-to-ambient quotient transport

`Langlands.fineAmbientQuotientTransport` proves exactly
`Langlands.FineAmbientQuotientTransportStatement.{uF,uV,uW,uZ}`.
The field and three representation-carrier universes remain independent.
The statement is imported from the published Library; this directory contains
only the separate proof pair.

The implemented proof starts with the two specified actual surjections `q₀`
and `q`. The source of `q₀` is smooth normalized refined induction, so
`isSmooth_of_surjective` supplies smoothness of the original coarse input `π`.
`refinedLeviRealTwist` transports that same `q₀` into the actual surjection
`qₜ` for the coarse twist with parameter `t`.

The proof applies the actual map `T.normalizedParabolicInducedMap B qₜ`.
Its surjectivity follows from
`normalizedInducedSurjectivity_of_smoothInductionSurjectivity` and the proved
`Induction.smoothInductionSurjectivity`. Smoothness of the source follows from
normalized refined induction, and smoothness of its target follows from
`T.isSmooth_leviRealPowerTwist_iff` and the already derived smoothness of `π`.

The fine ordinary inducing action `α` has exact determinant exponent
`-v₀ k + t ((B.flattenBlockEquiv S).symm k).1`; it is smooth by the same twist
smoothness theorem and the given smoothness of `ω`. The proof instantiates
`orderedRefinementInductionEquiv` at the canonical flattened block equivalence,
the inverse size equality, and `B.index_index_eq_flatten`. The actual canonical
Levi comparison is rewritten by `B.leviRefinementEquiv_flatten`, identifying
its iterated source with outer induction of the refined fine twist.

The resulting map is `q` composed with the induced `qₜ`, composed with the
inverse of this actual iterated-to-ordinary equivalence. Surjectivity is the
composition of the three surjectivity facts. The source is definitionally
`RelativeRecovery.fineAmbientInduced T B S ω v₀ t` and the target is the same
specified `J`. No chosen head or additional representation premise is used.

This is an internal composition of the imported Library constructions, with
upper normalized induction, right translation, positive-half covariance and
the existing normalized determinant twists retained. It supplies only forward
support transport, with no analytic recovery or classification conclusion.
