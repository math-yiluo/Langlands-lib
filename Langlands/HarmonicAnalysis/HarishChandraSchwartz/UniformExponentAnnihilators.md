# Uniform annihilators for labelled exponent families

This is an internal algebraic bridge for the proof of Waldspurger, *La formule de
Plancherel pour les groupes p-adiques d'après Harish-Chandra* (2003), Lemma VI.2.3,
printed p.300. The registered source is `waldspurger-2003-plancherel`. Its proof
uses finitely many exponent labels with fixed multiplicities and root moduli
independent of the unitary parameter. The present results formalize the
polynomial consequence of such data; they do not construct that data for the
actual induced orbit or prove the actual decay statement.

`HasUniformSplitAnnihilators j a F` is a proposition asserting that the already
defined `weakPart j (F ω)` and `positivePart j (F ω)` admit monic annihilating
polynomials for right translation by `j a`. Their degrees are independent of
`ω`; every weak root has norm one, and every positive root has norm at most a
single nonnegative real number strictly below one. This is the algebraic input
required by the published uniform projection and positive-part decay engines.

`weakPart_sum_labels` and `positivePart_sum_labels` identify those actual parts
of a finite sum of joint generalized eigenfunctions. The indexing type is an
arbitrary label type: the eigenvalue functions need not be distinct. The proof
places the two filtered sums in the weak and positive exponent submodules,
uses their independence via `weakPart_eq_of_mem`, and subtracts to identify the
positive part.

`hasUniformSplitAnnihilators_of_labelled_eigenfunctions` takes a fixed finite
label set, a fixed predicate classifying unitary labels, fixed natural-number
multiplicities, and a nonnegative bound for each positive label strictly below
one. The eigenvalue functions and eigenfunctions can vary over an arbitrary
parameter type. Joint generalized eigenspace membership and annihilation by the
displayed fixed power at `a` are explicit premises. The root bound applies
uniformly over all parameters. Zero multiplicities, empty label sets and
coincident specialized eigenvalue functions are allowed.

For each part the implemented proof forms the product of
`(X - C (χ ω i a)) ^ k i` over its labels. The degree is the sum of the fixed
multiplicities. The published `aeval_prod_apply_sum_eq_zero` proves
annihilation, and `exists_eq_of_mem_roots_prod` places every root among the
displayed eigenvalues. The common positive root bound is the finite supremum
of the fixed label bounds in `NNReal`; it remains strictly below one even for
the empty set, whose supremum is zero. Neither this proof nor the definition
requires a selected generic locus or injectivity of the specialized exponents.
