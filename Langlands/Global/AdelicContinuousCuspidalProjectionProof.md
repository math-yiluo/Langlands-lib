# Existence of continuous cuspidal projections

`Langlands.Global.continuousCuspidalProjectionExistence` proves
`Langlands.Global.ContinuousCuspidalProjectionExistenceStatement.{u}`
at arbitrary universe \(u\). For the standard parabolic quotient of
the statement, it constructs a continuous moderate-growth projection
with zero proper constant terms. At every ambient translate, pairing
with any Levi cusp form over the norm-one rational quotient converges
absolutely and agrees for the input and its projection.

The proof applies the projection assembly to
`leviRadicalAverageTestFunction` and `normOnePartialConvolutionRapidDecay`.
The former transfers adelic test functions through the radical integral.
The latter bounds the partial convolutions of cuspidal \(L^2\) classes
on norm-one representatives. These theorems discharge the two analytic
inputs of the assembly.

The construction uses a reproducing kernel for the input and the
finite right compact expansion of its translates. Finite Iwasawa
unfolding expresses the fibre pairings using averaged kernels.
The cuspidal Hilbert-space kernel vectors give the recentered scalar
pairings by Bochner integration. Smoothing the finite family gives
the ambient projection. Its moderate growth follows from height
bounds for the positive and norm-one factors of the Levi projection.
Its proper constant terms vanish by compact radical integration and
cuspidality of the smoothed classes. The norm-one transposition
of the kernel moves it to the cusp test, and the recentered expansion
gives equality of the pairings. The weighted bounds on rational
representatives give absolute convergence. The assembly treats
matrix size zero by taking the input itself as the projection on the
one-point adelic group.

The pairing statement is Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, JAMS 37 (2024), §6.2, p. 202,
equation (6.8). The proof uses the parabolic measure convention,
reproducing kernel, and cuspidal smoothing of Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series*, I.1.13, I.2.12,
I.2.17–18 and I.3.4–5.
