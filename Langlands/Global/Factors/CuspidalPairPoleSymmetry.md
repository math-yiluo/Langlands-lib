# Symmetry of the completed pair data

The global Rankin–Selberg integral for unequal ranks uses the larger rank
first. The finite and archimedean factors in `CuspidalPairPoleStatement`
can be compared under this interchange.

At a finite place the symmetric integral polynomial relation is invariant
under interchange, by `Padic.isPadicSymmetricLPolynomial_comm`. Applying it
to each pair of standard modules gives symmetry of the Langlands
certificate. The witnesses in the automorphic class relation can then be
interchanged. `FinitePairLChoice.swap` uses this certificate and retains
the additive character, measure and polynomial at every place. The finite
factor functions and the completed-product predicate consequently agree
for these two choices.

For the real and complex factors the proof writes each denominator as a
finite product over the two lists of blocks. Character multiplication
adds the exponents and the parities or weights. In the real case of two
induced blocks, the term with a conjugated character has the same exponent
after interchange, and its weight is negated. The complex Gamma shift only
uses the absolute weight, so this term also stays equal. Interchanging the
two finite products proves symmetry of the local factors and hence of their
product over the infinite places.

The published input is the pair product of local factors in J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §3.1, printed p. 213, and
§3.2, printed pp. 216–217 (PDF pp. 216 and 219–220). This file derives the
symmetry for the exact finite certificates and archimedean block formulas
used in the Library. The registered source `cogdell-2004-analytic-theory-gln`
has SHA-256 `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.

The real pair-factor symmetry comes from `RealPairLFactorNormalization`.
