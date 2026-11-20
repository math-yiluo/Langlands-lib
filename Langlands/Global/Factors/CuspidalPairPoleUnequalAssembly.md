# Unequal-rank assembly from normalized partial integrals

`UnequalNormalizedTests` is a family of vectors from the two actual cuspidal
realizations, both spherical outside a fixed set of finite places `S`.
The family comes with entire normalized factors with no common zero. On
right half-planes the corresponding partial Whittaker integrals are these
normalized factors times the finite local factors in `S` and the specified
archimedean factor. These normalization hypotheses are supplied inputs.

The proved unequal-rank unfolding theorem identifies the global integral
with the full Whittaker integral on an initial right half-plane. Partial
Euler factorization then supplies the product over the complement of `S`.
Absolute convergence of the full finite Euler product gives its value as
the product of the factors in `S` times the complementary product. This
matches each global test with its normalized factor times the initial
completed product.

The unequal-rank analytic theorem gives an entire continuation of every
global test integral and bounds it on vertical strips. Continuity of the
initial completed product on a right half-plane and the normalized family
now give a completed continuation by `exists_continuation_of_normalized_tests`.
The resulting profile has no poles. If a constant-coefficient finite
combination of the normalized factors is one, the same combination of
global integrals yields strip bounds for the continuation.

The proof implements the unequal-rank analytic assembly of J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §2.2, printed pp. 205–207,
§4.1, pp. 219–221, and §4.2, p. 222. The registered source
`cogdell-2004-analytic-theory-gln` has these passages on PDF pp. 208–210 and
222–225, with SHA-256
`8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The finite-combination transfer is the argument in §4.1 for adjacent ranks.
The premises leave room for another strip-bound proof for larger rank gaps.
