# Normalized finite tests on the exact factors of cuspidal presentations

For a specified pair L-choice and finite place, the actual integral
comparison identifies the chosen local polynomial with the JPSS
polynomial of the two finite components under the split-centre
hypotheses. After multiplication by this polynomial, the normalized
Laurent values have no common zero at the local spectral unit. The
Lean construction chooses an ordinary pair of Whittaker functions
and, in equal rank, a Schwartz–Bruhat function representing a rational
value with nonzero normalization at the supplied point. The entire
normalization is bounded on every closed vertical strip.

`PoleFiniteTestVectors` retains both Whittaker functions and their
realizations on the exact factors of the two spectral presentations.
Local genericity gives a one-dimensional functional space on each
component. Hence every selected coefficient belongs to the model
of a chosen nonzero functional. The first factor is obtained by the
published pullback along the finite equivalence. For the second
factor, the proof transports the functional to the canonical inverse
additive component. The same input vector to the two model maps gives
the original coefficient pointwise. Each realization includes a
reference vector with functional value one, as required by the finite
tensor separation theorem.

The local fractional-ideal result is in H. Jacquet, I. I.
Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg convolutions*
(1983), Theorem 2.7(ii), printed pp. 390–391 (PDF pp. 25–26).
The use of local Whittaker models and the normalized test product is
in J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
§3.1, printed p. 213 (PDF p. 216), and §4.1, p. 220 (PDF p. 223).
The Lean proof performs the finite local selection and transport.

## Finite bounded combinations

`poleFiniteBoundedTestFamilies` realizes the whole bounded combination of
ordinary normalized rational zeta values on the same two prescribed tensor
factors. Each indexed rational value comes from an actual local test.
Realize both coefficients by the same local multiplicity-one argument and
take the regularized Laurent value as its normalization. The combination
from the finite local L-polynomial is unchanged by this choice of witnesses,
and its Laurent weights are bounded on vertical strips. This applies in
equal rank and in the ordinary integral at every positive rank gap.
