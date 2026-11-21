# Continuing the normalized unequal-rank equation in the larger exponents

Fix the smaller Whittaker vector and the angular weights of the larger standard module. Let the larger inducing exponents vary holomorphically with \(z\). If every larger canonical Jacquet value satisfies the exact normalized equation against the fixed smaller vector near \(z=0\), `complexUnequalCanonicalReflection` gives the equation for every larger canonical value at \(z=1\).

Start with a larger standard vector at the endpoint and use its compact profile throughout the parameter disk. `complexUnequalCanonicalFamily` gives joint holomorphy of both raw integrals on a common right half-plane. On each initial slice, use the assumption with the standard vector transferred to that slice. `complexPairParameterReflection` continues these normalizations to the endpoint, with the fixed central sign and the exact complex epsilon factor. Transferring the vector at its own parameter recovers the starting vector.

This is the continuation step used after a chamber calculation of the unequal-rank equation. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8.1](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

`complexUnequalCanonicalGrowthReflection` preserves exponential strip growth for both functions. It uses uniform bounds for the ordinary and dual raw integrals on the parameter disk and closed strips on the right. The strip-growth reflection theorem transports these bounds through reciprocal Gamma normalization and the continuation in the larger inducing exponents.
