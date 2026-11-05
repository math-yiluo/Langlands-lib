# Laurent polynomials along orthogonal idempotent matrices: the closure argument

Author: Worker 1532. Uses `ExponentialPolynomial` by Worker 1045.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement`. It is pure algebra over the explicit
coordinate ring `GeneralLinear.CoordinateRing n K` of `GL_n` and its classifying maps
`GeneralLinear.classify`. Its two main theorems say that an ideal killed by suitable powers of a
point is killed by its "semisimple part"; this is the algebraic content of the statement that
the Jordan parts of a point of a closed subgroup of `GL_n` lie in the subgroup.

## Block-scalar matrices

For a complete family of orthogonal idempotent matrices `E : Fin r → Matrix n n K` and a
commutative `K`-algebra `S`:

- `diagMatrix E t = ∑ i, t i • E i` (with `E i` mapped to `S`); `diagMatrix_mul`,
  `diagMatrix_one`, using the general `sum_smul_mul_sum_smul` for orthogonal idempotents.
- `diagHom hE S : (Fin r → Sˣ) →* GL n S`, `diagHom_val`, and `map_diagHom`: an algebra map
  `S →ₐ[K] S'` sends `diagHom t` to `diagHom` of the mapped units.

## Laurent polynomials

`Laurent K r` is `AddMonoidAlgebra K (Fin r → ℤ)`. `charHom t a = ∏ i, t i ^ a i` is the
character of the exponent lattice at units `t`, with `charHom_pow`; `evalLaurent t` is the
evaluation algebra map; `genericUnit i` is the monomial unit `X i`, with
`evalLaurent_genericUnit`; and `evalLaurent_eq_sum` writes an evaluation as a finite sum over
any superset of the support. `laurentPoint hE = diagHom hE (Laurent K r) genericUnit` is the
generic block-scalar point, and `evalLaurent_comp_classify` says its classifying map followed by
`evalLaurent t` is the classifying map of `diagHom hE K t` (by `classify_map`).

## Grouping by values

- `eq_zero_of_finset_sum_mul_pow_eq_zero` and `eq_zero_of_finset_sum_pow_mul_eval_eq_zero` are
  the Finset forms of Worker 1045's `eq_zero_of_sum_mul_pow_eq_zero` (Vandermonde) and
  `eq_zero_of_sum_pow_mul_eval_eq_zero` (exponential polynomials, characteristic zero), indexing by
  the elements of the finset.
- `sum_mul_eq_zero_of_pow`: if `x ↦ x ^ q` is injective on `K` and
  `∑_{a ∈ S} c a (g a ^ q) ^ k = 0` for all `k : ℕ`, then `∑_{a ∈ S} c a g a = 0`. Group the terms
  by the value `v = g a ^ q`; Vandermonde gives that each group sum of coefficients vanishes;
  injectivity of the `q`-th power makes the fibres of `g` the same as those of `g ^ q`.
- `sum_mul_eval_eq_zero` (characteristic zero): if `g a ≠ 0` and
  `∑_{a ∈ S} g a ^ k * (Q a)(k) = 0` for all `k : ℕ`, then `∑_{a ∈ S} g a * (Q a)(τ) = 0` for every
  `τ`. Group by the value of `g`; the exponential-polynomial lemma kills every group polynomial.

## Positive-characteristic closure

`classify_diagHom_eq_zero_of_pow`: let `I` be an ideal of the coordinate ring, `lam : Fin r → Kˣ`
and `q` with `x ↦ x ^ q` injective. If `classify (diagHom ((lam ^ q) ^ k))` kills `I` for every
`k : ℕ`, then `classify (diagHom lam)` kills `I`. Proof: for `f ∈ I`, the Laurent polynomial
`ℓ = classify (laurentPoint hE) f` satisfies `evalLaurent t ℓ = classify (diagHom t) f`; expand
both evaluations as sums over the support and apply `sum_mul_eq_zero_of_pow`.

## Characteristic-zero closure

- `binomPoly i = X (X - 1) ⋯ (X - i + 1) / i!`, with `binomPoly_eval_natCast` (value `k.choose i`
  at `k`, characteristic zero), `binomPoly_eval_zero` and `binomPoly_zero`.
- `binomMatrix N m = ∑_{i ≤ m} binomPoly i • N ^ i` over `K[X]`. If `N ^ (m + 1) = 0` its
  evaluation at `k` is `(1 + N) ^ k` (`sum_binomPoly_eval_natCast`, binomial theorem), at `0` is
  `1` (`sum_binomPoly_eval_zero`), and it is a unit (`isUnit_binomMatrix`: it is `1` plus `N`
  times a polynomial in `N`, which is nilpotent).
- `evalLX t τ` evaluates `(Laurent K r)[X]` at `(t, τ)`; `evalLX_eq_sum` expands it as
  `∑_a charHom t a * (lxCoeffPoly ℓ a)(τ)` over `lxSupport ℓ`. `laurentPolyPoint hE U` is
  `laurentPoint` times the image of `U : GL n K[X]`, and `evalLX_comp_classify` identifies its
  evaluations with `classify (diagHom t * U(τ))`.
- `classify_diagHom_eq_zero_of_unipotent` (`CharZero K`): let `u : GL n K` with
  `(u - 1) ^ (m + 1) = 0`. If `classify (diagHom (lam ^ k) * u ^ k)` kills `I` for every `k : ℕ`,
  then `classify (diagHom lam)` kills `I`. Proof: with `U = binomMatrix (u - 1) m`, the hypothesis
  says `∑_a charHom lam a ^ k * (lxCoeffPoly ℓ a)(k) = 0` for all `k`; `sum_mul_eval_eq_zero`
  gives the vanishing at `τ = 0`, where `U(0) = 1`.
