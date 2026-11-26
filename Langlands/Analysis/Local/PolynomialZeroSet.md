# Null zero sets of multivariate polynomials

The lemma `Langlands.Analysis.ae_eval_ne_zero` concerns a nonzero polynomial over a field
with a Borel topology. It gives almost-everywhere nonvanishing for the product of a
sigma-finite measure that gives every singleton measure zero.

The proof inducts on the number of variables. The leading coefficient of the polynomial
in the first variable is a nonzero polynomial in the remaining variables. By induction it
is nonzero for almost every choice of those variables. Each such specialization has only
finitely many roots. Fubini and the first-coordinate splitting of finite product measure
give the result. The argument is an internal measure-theoretic ingredient for the Haar
conullity of the ordinary and twisted regular loci.
