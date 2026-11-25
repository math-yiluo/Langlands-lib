# Geometric rank and extension of integral prime traces

This internal construction proves the geometric rank clauses and
reduces the full trace comparison to common rational values on actual integral
endomorphisms. All fields and schemes retain the arbitrary universe `u`.

`primeTate_finiteDimensional` proves finite dimensionality of the actual
rational prime Tate module of every actual abelian scheme over an algebraically
closed characteristic-zero field. Connectedness of the source follows from
geometric connectedness over a field. The published
`smoothConnectedRelativeDimension` supplies a relative dimension, and
`Tate.PrimeAdic.geometricPrimeAdicRank` supplies finite dimensionality.
`primeTate_finrank` gives rank `2 * g` for each supplied relative dimension `g`.
The prime is a unit in the field by characteristic zero, and the
`Scheme.ΓSpecIso` transports this fact to global sections.

`integralPrimeTrace A p` restricts the existing actual rational prime trace
along `homToHom0`; it is an integer-linear map on the actual endomorphism
group. Suppose every integral endomorphism has a rational trace value common
to all primes. Tensor induction on `End0 A = ℚ ⊗[ℤ] End A` extends these common
values to all rational endomorphisms. `rationalTraceOfIntegral` chooses these
values. Injectivity of `ℚ → ℚ_[2]` and linearity of the actual 2-adic trace prove
that the resulting map is rational-linear. Its specification is agreement
with every prime trace.

`comparison_of_integral` combines this extension with the two rank results.
The published uniqueness theorem `geometricEndomorphismTrace_eq` identifies
the constructed rational-linear lift with the fixed `geometricEndomorphismTrace`.
The conclusion is the complete unchanged
`GeometricEndomorphismTraceComparisonStatement.{u}`. The common rational
integral-trace hypothesis remains explicit and unproved here, so this is a
conditional reduction, not a proof of that target.

The provenance is internal: the argument composes the named published
geometric rank and relative-dimension theorems with tensor induction and
injectivity of rational scalars. No characteristic-polynomial theorem,
geometric trace rationality, or prime independence is supplied by this module.
