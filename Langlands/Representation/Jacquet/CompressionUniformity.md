# Uniform compression from qualitative stability

Worker 1751. This is an internal reduction for Renard VI.9.1, based on the
published compact compression, fixed-exponent interface, C.II stability laws,
and actual smooth direct sums. It assumes eventual stability on every smooth
representation. It does not establish that representation-theoretic hypothesis.

The source context is Renard 2026, Appendix C.II, Definition and Lemma (i),(iv),
printed pp.276–278 / PDF pp.282–284, and VI.9.1 Proposition, printed p.197 /
PDF p.203. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retract and diagonal reductions below are derived internal results; they
are not additional assertions attributed to Renard.

`PointwiseCompressionEventuallyStable` means that every smooth complex
representation in the specified carrier universe has a positive stable power of
the compressed action for the fixed compact open subgroup and group element.
`UniformCompressionStationary` is existence of a natural-number threshold chosen
before all such smooth objects, from which both power chains equal their limits
and the kernel supremum and stable image are complementary.

`stable_of_retract` proves that stability descends to an endomorphism retract.
Its kernel argument embeds a vector killed by the square, uses stability in the
larger space, then projects. Its range argument embeds a vector in the range,
lifts it through the larger square, and projects that lift. Applying compression
naturality and its power form gives
`compactCompressionStablePower_of_retract` with exactly the same exponent.

`uniformCompressionStationary_of_pointwise` argues by contradiction. For every
proposed threshold b it chooses a smooth representation A(b) failing the
stationary-chain conclusion at b. The actual algebraic direct sum of this
countable family is smooth. The pointwise hypothesis supplies a positive stable
power b on this sum. Each summand is an actual equivariant retract, so the same
power is stable on A(b). The fixed-exponent interface then gives stationarity
starting at b, a contradiction. The direct sum is indexed by natural numbers,
so its carrier has the original carrier universe. The group universe is
independent and no dimension or admissibility condition is used.

`pointwiseCompressionEventuallyStable_iff_uniform` adds the converse using the
published equivalence between eventual stability and an existential stationary
threshold. This is a qualitative reduction only: dynamic-parabolic geometry,
centrality and contraction must still prove eventual stability on every smooth
object before this result can discharge the uniform theorem. The countable-sum
argument is an internal proof route and is not attributed to the original
source's quantitative bound.
