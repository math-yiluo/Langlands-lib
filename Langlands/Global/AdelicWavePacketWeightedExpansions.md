# Finite weighted expansions on a common spectral domain

`WavePacketWeightedExpansionsStatement` combines finite expansions of
the individual terms of a weighted family. The outer index is finite,
and its allowed vectors are specified by a predicate containing the
zero vector at each index. Each original expansion has meromorphic
coefficients on a domain of holomorphy containing the supplied
spectral set. The weights are entire, and the regularity conditions
are nested as the real threshold increases.

`wavePacketWeightedExpansions` intersects the domains, taking the
whole parameter space for expansions of length zero. It pads the
expansions to the maximum length with zero coefficients and zero
vectors. The weights multiply the padded coefficients on the common
domain. The product of the original term index and the padded index
gives one finite index for the expansion of the weighted sum. For
each outer index the proof takes a common upper bound for its finite
set of regularity thresholds and distributes the weights over the
sums. The resulting expansions have the same length and domain and
preserve the allowed-vector predicates.

The construction applies to the intertwining expansions in E. Lapid,
*On Arthur's asymptotic inner product formula of truncated Eisenstein
series*, Clay Math. Proc. 13 (2011), §2, p. 312 (volume PDF p. 321).
In the pairing of §8, p. 328, the predicate specifies the
square-integrable inducing vectors of each target parabolic.
