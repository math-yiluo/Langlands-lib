# Proof that trace-class operators are Hilbert–Schmidt

The theorem `Langlands.Analysis.OperatorIdeals.traceClassHilbertSchmidt`
proves `TraceClassHilbertSchmidtStatement` for every complete complex
inner-product space, retaining its arbitrary universe and allowing
nonseparable spaces.

This is an internal proof using the concrete definitions in
`OperatorIdeals`. The statement Markdown supplies the original Getz–Hahn
passages, exact source fingerprints, left-modulus convention and the
derived arbitrary-index scope. The proof does not import an unproved
operator-ideal or basis-independence target.

First, continuous functional calculus proves
`L * L = A * star A` for `L = leftModulus A`. For any positive bounded
operator `T`, put `B = CFC.sqrt T`. Positivity implies self-adjointness
of `B` and `B * B = T`. The adjoint identity gives
`‖B x‖² = Re⟪x, T x⟫`. Applying the operator norm bound to `B (B x)`
and squaring yields
`‖T x‖² ≤ ‖B‖² Re⟪x, T x⟫`.
The same adjoint identity and `L² = A A*` give
`‖A* x‖² = ‖L x‖²`.

Choose the basis witnessing `IsTraceClass A`. The preceding estimates
bound the nonnegative squared-image family of `A*` by a constant times
the summable modulus diagonal. The comparison theorem for real
summable families proves square summability of `A*`.

To transfer back to `A`, the proof writes each squared image norm as
the extended nonnegative sum of its squared basis coefficients.
Parseval comes from the actual Hilbert-basis isometry into `lp 2`.
Exchanging the two extended sums and using the adjoint identity equates
the squared-image totals of `A` and `A*` on this same basis. The latter
total is finite, so conversion from the extended sum proves real
summability of the former. This supplies the basis witness for
`IsHilbertSchmidt A`.

All auxiliary lemmas are private. The only additional public theorem is
`isHilbertSchmidt_of_isTraceClass`, the direct implication used to assemble
the exact proposition target. No countable enumeration, separability,
spectral decomposition or pre-existing trace-class ideal theorem is used.
