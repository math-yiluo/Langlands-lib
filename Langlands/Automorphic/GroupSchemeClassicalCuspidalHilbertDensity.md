# Classical density in the full cuspidal Hilbert space

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeClassicalCuspidalHilbertDensity`
proves `GroupSchemeClassicalCuspidalHilbertDensityStatement`. For a connected
reductive affine locally finite-type group over a number field, fix a smooth
relative dimension, a compact subgroup at infinity and a closed matrix
representation of positive size. The central morphism from a specified
finite split torus has injective rational-character restriction with
finite-index image. The parabolic-dynamic assertion specifies the radical
family for the full cuspidal space. The density theorem assumes right
invariance of norm-one Haar measure to form the integrated right action
in its proof. Assume archimedean conjugation fixes the enveloping center.
Every class of the full cuspidal Hilbert space is approximated in its Hilbert
norm by classes with a continuous representative on the positive rational
quotient whose adelic pullback satisfies `IsAutomorphicFunctionOn` and has
all proper normalized periods zero. The pullback is smooth on every infinite
slice and right invariant throughout the adelic group under one open
subgroup of the finite adelic group, which may depend on the representative.
It is finite under the specified compact subgroup and the complex enveloping
center, and has uniform polynomial height growth for all the real
directional derivative words.

The proof forms the subspace of classes with these finite orbit and growth
conditions. Linearity of the directional-word enveloping operators and taking
the maximum of two growth exponents give closure under addition. For a nonzero
vector orthogonal to the subspace, take a normalized nonnegative compact
smooth kernel supported where its orbit is within half its norm. The kernel
is invariant under inversion and under conjugation by the compact subgroup.
Its integrated operator is compact and symmetric and commutes with the
subgroup. Every nonzero eigenspace belongs to the subspace. The operator
applied to the orthogonal vector is then orthogonal to those eigenspaces by
symmetry and to the zero eigenspace by the kernel equation. The compact
spectral theorem forces the output to vanish, contradicting the orbit estimate.
Pointwise cuspidality of the approximating representatives follows from the
full cuspidal Hilbert condition.

The density step is used in Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.3.4, p. 46. Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), §9.3, pp. 246–248, around (9.12)–(9.13),
describes symmetric mass-one approximations, the compact spectral theorem
and the Hilbert–Schmidt estimate from bounded point evaluations. Here the
actual adelic convolution has global height growth, and cuspidal rapid
decay and uniform boundedness control its point evaluations. This supplies
the compact operator used in the density argument.
