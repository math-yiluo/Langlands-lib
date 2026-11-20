# Independence of the finite pair L-data

The pair L-polynomials in `FinitePairLChoice` have certificates built through
Langlands standard modules. To compare two polynomials for the same pair, choose
one standard module for each representation and evaluate both certificates on
that pair. Two continuous nontrivial additive characters on the same p-adic
field differ by scaling by a unit of the field. The theorem
`Padic.isPadicSymmetricLPolynomial_characterChange` transports the first
certificate under this scaling. Then `IsPadicSymmetricLPolynomial.unique_of_measure`
compares the two normalized generators for their supplied additive Haar measures.
Representatives of the two automorphic classes reduce the class version to this
comparison through `isAutomorphicPairLPolynomial_iff`.

`FinitePairLChoice.of_localClass_eq` transports certified data between
presentations whose finite local classes agree at every place. The pointwise
lemma `finiteL_eq_of_localClass_eq` needs class equality only at the place in
question and compares any two finite-data choices. This permits comparison with
the standard adelic additive character at the exceptional places and transfer
of the finite Euler product along equivalences of cuspidal realizations.

The additive-character independence is the consequence of the fractional ideal
construction described in J. W. Cogdell, *Analytic theory of L-functions for
GL_n* (2004), §3.1, p. 213, immediately before Theorem 3.1. The registered source
`cogdell-2004-analytic-theory-gln` has this passage on PDF p. 216, with SHA-256
`8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The class and spectral-presentation forms are derived in the Library's
vocabulary from the standard-module comparison above.
