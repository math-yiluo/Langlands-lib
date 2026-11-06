# The monomial basis of binary homogeneous polynomials

Worker 1628 builds this internal construction at the request of Worker 1369
(an executor of task 2d982376). It is the standard monomial basis of the
binary forms of degree `m`, written with explicit indices. No literature claim
is made.

## Setting

Let `R` be a commutative semiring and `m` a natural number. The binary
homogeneous polynomials of degree `m` form Mathlib's
`homogeneousSubmodule (Fin 2) R m`, the `R`-submodule of the polynomials in
`MvPolynomial (Fin 2) R` that are homogeneous of degree `m`. The variables are
`X 0` and `X 1`.

## Declarations

All declarations are in the namespace `Langlands.GroupScheme.HomogeneousPolynomial`.

- `binaryExponent m c`, for `c : Fin (m + 1)`, is the exponent
  `single 0 c + single 1 (m - c)`, the exponent of the monomial
  `X 0 ^ c * X 1 ^ (m - c)`. The lemmas `binaryExponent_apply_zero` and
  `binaryExponent_apply_one` give its two entries, `degree_binaryExponent`
  shows that its total degree is `m`, and `binaryExponent_injective` shows that
  `binaryExponent m` is injective.
- `binaryExponentEquiv m` is the bijection between `Fin (m + 1)` and the
  exponents `d : Fin 2 →₀ ℕ` of total degree `m`. It sends `c` to
  `binaryExponent m c`, and its inverse sends `d` to `d 0`. Since
  `d 0 + d 1 = m`, the entry `d 1` is `m - d 0`.
- `binaryBasis m : Module.Basis (Fin (m + 1)) R (homogeneousSubmodule (Fin 2) R m)`
  is the monomial basis. It is built from Mathlib's
  `basisRestrictSupport R {d | d.degree = m}`, the monomial basis of
  `restrictSupport R {d | d.degree = m}`, the polynomials supported on
  exponents of degree `m`. Mathlib's
  `homogeneousSubmodule_eq_finsupp_supported` identifies these polynomials with
  the homogeneous submodule. The basis is then reindexed by
  `binaryExponentEquiv m`.
- `binaryBasis_repr_apply` (coefficient extraction): the `c`-th coordinate of
  `p` in this basis is the coefficient of `p` at `binaryExponent m c`, that is,
  the coefficient of `X 0 ^ c * X 1 ^ (m - c)`. This holds by definition.
- `binaryBasis_apply_eq_monomial` and `binaryBasis_apply`: the `c`-th basis
  vector, as a polynomial, is `monomial (binaryExponent m c) 1`, which equals
  `X 0 ^ c * X 1 ^ (m - c)`. Proof: by `Module.Basis.apply_eq_iff`, it suffices
  that the coordinates of this monomial form the indicator function of `c`. That
  follows from coefficient extraction and the injectivity of `binaryExponent m`.
- `coeff_binaryBasis`: the coefficient of the `c`-th basis vector at an
  exponent `d` is `1` if `d = binaryExponent m c` and `0` otherwise.
- `aeval_binaryBasis` and `eval_binaryBasis`: evaluating the `c`-th basis vector
  at `x : Fin 2 → S` gives `x 0 ^ c * x 1 ^ (m - c)`. The first lemma holds in
  any commutative `R`-algebra `S`, and the second is the case `S = R`.
- `eq_sum_binaryBasis`: every `p` in the submodule equals
  `∑ c, C (coeff (binaryExponent m c) p) * (X 0 ^ c * X 1 ^ (m - c))`, summed over
  `c : Fin (m + 1)`. This is the basis expansion `Module.Basis.sum_repr`,
  rewritten with coefficient extraction and the formula for the basis vectors.

## Scope

The file makes no claim about group actions, representations of `SL₂` or
irreducibility. It only fixes the indexing of the monomial basis.
