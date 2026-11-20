# Finite data and the Euler product for cuspidal pair poles

`standardFinitePairLChoice` assembles the finite data in `CuspidalPairPoleStatement`
and supplies the witness for `nonempty_finitePairLChoice`.
The proof uses the adelic additive character from `CuspidalWhittaker.AdelicCharacter`,
which is nontrivial and trivial on the diagonally embedded number field. At each
finite place take its canonical local restriction, its self-dual additive Haar
measure, and the pair L-polynomial supplied by `exists_isAutomorphicPairLPolynomial`.

For any certified choice, `FinitePairLChoice.finiteL_eq_partialEulerFactor` compares
the finite factor at a place outside the two exceptional sets with the corresponding
spherical factor used in the global Euler factorization. It uses each presentation's
spherical spectrum and the local polynomial comparison in `CuspidalPairFiniteLayer`.
The comparison works for the additive characters and self-dual measures of the supplied
choice. No agreement with the standard adelic character is a hypothesis.

`FinitePairLChoice.exists_finiteL_convergence` applies `exists_partialEulerFactor_convergence`
to the complement of `S`, then adjoins the finitely many factors at places in `S`.
`FinitePairLChoice.isCompletedLFunction_of_partialEulerProduct` intersects this convergence
half-plane with the half-plane on which the completion agrees with the product formula.

This is the finite Euler product step in J. W. Cogdell, *Analytic theory of L-functions
for GL_n* (2004), §3, Theorems 3.1 and 3.3 (pp. 213 and 215), and §4, pp. 218–219.
The registered source `cogdell-2004-analytic-theory-gln` has these passages on PDF pp.
216, 218 and 221–222, with SHA-256
`8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The Lean lemmas give the comparison and convergence for the exact finite data in the target.
