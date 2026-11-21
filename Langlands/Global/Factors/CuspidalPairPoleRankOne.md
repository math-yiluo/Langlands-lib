# Completed cuspidal pair L-functions in rank one

`CuspidalPairPoleRankOneAt` restricts `Langlands.Global.CuspidalPairPoleStatement`
to pairs of `GL₁` realizations over a fixed number field with compact adele
quotient. It retains the split-centre and presentation hypotheses, the two
universes, and the quantification over all certified finite L-data and all
archimedean parameter families. The result includes existence of these data,
right-half-plane identification with the completed Euler product, the exact
two-point pole profile, and bounds on every vertical strip away from the
specified discs.

The proof uses `nonempty_finitePairLChoice` and `cuspidalArchimedeanParameterPartial`
for the data. For the standard adelic additive character, a common retained set
supports the finite character and both presentations. The single ordinary test
from `rankOneConstantNormalizedTest` has nonzero constant normalization. For
an actual conjugate pair, the common set also contains the places needed for
the normalized residue test. Ordinary rank-one local continuation normalizes
the pure tests of the chosen Schwartz tensor. Bilinearity supplies the
normalization on the two finite spans, including the nonzero vector paired with
its conjugate. The Schwartz and Fourier values at zero are both nonzero.

The covering family includes these tests. The constant normalization gives
pointwise coverage. The fixed-rank completion theorem glues the continuation
using the normalized test identities and transports a contragredient pair to
the actual conjugate pair. On that pair the determinant-slab period of the
residue test is positive, so the two origin values detect both simple poles.
In the other case a nonzero residue would give a contragredient pairing, so the
completed function has no poles. The raw integral of the constant-normalized
test is bounded on each strip away from the two discs. Dividing its bound by
the norm of the nonzero constant gives the bound for the completion.

This implements the equal-rank unfolding, continuation and residue argument
of J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.3,
printed pp. 208–211, §4.1, pp. 219–221, and Theorem 4.2, p. 222. The
rank-one test is obtained from the implemented scalar Tate tests at the
finite and infinite places. The fixed-rank continuation helpers specialize
Worker 679's ordinary pure tensor and conjugate residue constructions. The
pole locations and the split-centre hypothesis are those in Getz and Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 11.7.1,
printed p. 309.
