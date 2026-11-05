# Unique factorization in the actual unramified scalar algebra

This is an internal algebraic construction supporting the conditional standard
intertwining project. Its provenance is the published finite Laurent-algebra
equivalence and Mathlib's polynomial and localization results. No new external
representation-theoretic assertion is used.

`finiteLaurentSuccessorEquiv R n` identifies the additive group algebra of
`Fin (n + 1) → ℤ` over a commutative ring `R` with the one-variable Laurent
polynomial ring over the additive group algebra of `Fin n → ℤ`. It separates
the first coordinate using `Fin.consEquiv`, transports the group algebra
along that additive equivalence, and applies `AddMonoidAlgebra.curryRingEquiv`.

`laurentPolynomial_uniqueFactorizationMonoid` uses the polynomial UFD result
and `LaurentPolynomial.isLocalization`, which identifies the Laurent polynomial
ring with localization at the powers of the polynomial variable. Mathlib's
`UniqueFactorizationMonoid.of_isLocalization` supplies unique factorization.

`finiteLaurent_uniqueFactorizationMonoid` then proceeds by induction on the
finite rank. The zero-rank group algebra is the coefficient ring by
`AddMonoidAlgebra.uniqueRingEquiv`. The successor equivalence and the Laurent
localization result give the induction step.

For an actual connected reductive group scheme `G` over an arbitrary
nonarchimedean local field, with a supplied rational-point topology and
continuity of `rationalValuationImageProjection G`,
`rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid` transports this
result through the published `rationalUnramifiedLaurentAlgebraEquiv`.
Its target is precisely the existing evaluation-generated complex algebra for
the full rational norm family, rather than a replacement formal scalar ring.
The rank may be zero; there is no restriction on characteristic, splitness or
quasisplitness.

`rationalUnramifiedRegularFunctions_exists_prime_factors` specializes Mathlib's
finite prime factorization result: every nonzero element of this actual algebra
is associated to a finite product of prime elements. Association allows a unit
factor, and an empty product covers units.

These are scalar algebra results. They do not prove analytic divisibility,
removal of denominator factors, any assertion that a nonzero regular function
is nonzero at every character, an operator's rationality, convergence, or the
whole conditional standard intertwining theorem. Those remain separate
obligations.
