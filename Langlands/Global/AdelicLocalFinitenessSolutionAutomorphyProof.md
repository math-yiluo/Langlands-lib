# Automorphy of solutions of the local-finiteness system

`Langlands.Global.localFinitenessSolutionAutomorphy` proves
`LocalFinitenessSolutionAutomorphyStatement`. It applies
`localFinitenessSolutionAutomorphy_of` with `uniformGrowthLocalFiniteness`
and with `localFinitenessCenterStability_of adelicEnvelopingCenterConjugation`.

Conjugation invariance of the enveloping center makes its action commute with
right convolution. The action also commutes with the unipotent constant terms
and left translations in the polynomial equations, so it preserves the entire
solution space. The local-finiteness theorem puts the solutions into a
finite-dimensional range at a possibly larger growth exponent. The inclusion
between the two growth spaces preserves the underlying functions and hence
the equations, so the enveloping-center orbit of a solution lies in that range.

At each parameter an equation with nonzero scalar coefficient expresses a
solution as a linear combination of its convolutions with finitely many
kernels. Right compact translation of a convolution acts by left translation
of the kernel. Each span of translated kernels is finite-dimensional, which
gives right compact finiteness of the solution. Rational left invariance,
smoothness and moderate growth follow from the uniform-growth carrier.

This is the center-finiteness and compact-finiteness argument in the converse
direction of the lemma in §8.1 of J. Bernstein and E. Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), p. 222 (PDF p. 36), applied to the admissible system
\(\Xi_{\mathrm{main}}\) of §7.2, pp. 211–212 (PDF pp. 25–26), whose
local-finiteness theorem is on p. 212. The registered journal PDF is
`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`, SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
