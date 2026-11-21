# Preservation of strip growth under parameter continuation

`CompactParameterStripGrowthStatement` concerns holomorphic traces on
opposite spectral half-planes over a bounded parameter disk. Both traces
have a common exponential rate in the spectral imaginary part, with a
constant allowed to depend on the real strip. On an initial parameter
disk they agree with entire functions that have exponential strip
growth. At parameter one they then agree with an entire function that
also has exponential strip growth.

The continuation theorem first gives the entire function at parameter
one. On the initial disk, Phragmén–Lindelöf bounds the entire functions on
each real strip with uniform slope `1 + K² / 4`, where `K` is the common
trace rate. After translating by `iT` and multiplying by
`exp(−(1 + K² / 4) |T|)`, the bounds on every fixed spectral circle are
uniform in `T`. Cauchy estimates give uniform Taylor coefficient bounds.
The coefficients are holomorphic in the parameter, and decay at every
geometric rate on the initial disk. To propagate decay uniformly in
`T`, the proof picks a height with a violating coefficient whenever such
a height exists and applies the Library's coefficient decay theorem to
that sequence.

The Taylor coefficients of the translated continuation at parameter one
agree with these coefficients by the right trace identity. Evaluation
at the real part of a spectral point, using its imaginary part as `T`,
bounds the weighted continuation by a summable geometric majorant plus
finitely many terms. Removing the weight gives the claimed strip bound.

This is an internal quantitative continuation tool for the vertical
strip estimates in Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), §8.1, pp. 53–54.
