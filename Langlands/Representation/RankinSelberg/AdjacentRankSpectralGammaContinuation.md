# Explicit spectral gamma product continuation

This internal specialization constructs the finite kernels needed by
`AdjacentRankGammaEntireContinuation` directly from two fixed rational functions
`G₀` and `G₁`. It makes no claim that either function is a gamma factor of a
representation.

The parameterized rational product is
`G₀(X) * G₁(q^(-u) X)`. Its displayed numerator is the fixed numerator of `G₀`
times the spectrally rescaled numerator of `G₁`; its displayed denominator uses
their denominators in the same way. These are the actual
`spectralClearingKernel` families. The rational numerator-denominator identity
and the algebra automorphism `rationalRescale` prove the finite presentation.
The denominator kernel is nonzero for every complex parameter because each
fixed denominator is nonzero and polynomial rescaling is an automorphism.
Both kernels have entire coefficients and one common finite support by the
existing spectral-kernel theorem.

The final theorem takes entire original and dual coefficient families, their
actual rational continuations and absolutely convergent spectral expansions,
real-ray finite clearing by the product of a fixed polynomial and a rescaled
fixed polynomial, and gamma equations for the displayed spectral product on
that ray. The retained-kernel entire-continuation theorem gives the gamma
equation at zero. Polynomial clearing is nonzero there when the supplied
polynomial product is nonzero. Spectral rescaling at zero is the identity, so
the resulting factor is exactly `G₀ * G₁`.

This proof discharges the analytic finite-kernel presentation and nonvanishing
inputs for the displayed product. Constructing actual representation families,
their gamma certificates on the real ray, and unramified gamma transport
remains outside this scalar specialization.
