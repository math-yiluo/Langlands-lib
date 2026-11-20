# Evaluating the normalized p-adic zeta values

`IsNormalizedGenerator.normalizedLaurent` takes a member of the local zeta span
and returns its Laurent polynomial after multiplication by the certified
L-polynomial. The membership and normalization hypotheses give existence of
this polynomial. Injectivity of the Laurent embedding in the rational field
ensures uniqueness and proves linearity over the Laurent coefficient ring.

`exists_laurentEval_normalizedLaurent_ne_zero` evaluates these normalized
values at a nonzero complex spectral point. If the values from every test
vanished there, so would every Laurent linear combination of them. The
reciprocal of the L-polynomial belongs to the same span and normalizes to one.
Consequently at every nonzero spectral point at least one normalized test
has nonzero value.

Evaluation at `q^(-s)` gives an entire function of `s` for `q > 1`. The
spectral point is entire and never zero, so this holds for every Laurent
polynomial. If a test has a rational continuation, on a sufficiently far
right half-plane the test equals the evaluated normalization times the
reciprocal of the L-polynomial. The cleared identity follows from evaluation
of the rational functions where regular. The half-plane can also be chosen
to avoid the zeros of the L-polynomial since its constant coefficient is one.

The fractional ideal and the absence of a common zero for normalized tests
are described in J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
§3.1, Theorem 3.1 and the two paragraphs following it, p. 213. The registered
source `cogdell-2004-analytic-theory-gln` has these passages on PDF p. 216,
with SHA-256 `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
This is the algebraic evaluation step for a supplied normalized generator.
