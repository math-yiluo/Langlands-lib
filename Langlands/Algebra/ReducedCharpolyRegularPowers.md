# Regular elements of central simple algebras: minimal polynomials and powers

Module: `Langlands.Algebra.ReducedCharpolyRegularPowers`, namespace `Langlands.CentralSimple`.

## Polynomial evaluation in an algebra

Here `K` is a commutative ring (a field where stated) and `A` a `K`-algebra, not necessarily
commutative.

- `isUnit_aeval_derivative_of_separable`: if `g` is separable (`IsCoprime g g'`) and
  `g(a) = 0`, then `g'(a)` is a unit. Evaluating a Bézout identity `p g + q g' = 1` at `a` gives
  `q(a) g'(a) = 1`; polynomials in `a` commute, so `q(a)` is a two-sided inverse.
- `aeval_inv_reflect_mul_pow`: for a unit `u` of `A` and `natDegree f ≤ N`,
  `(reflect N f)(u⁻¹) uᴺ = f(u)`. Induction over the monomials of `f`
  (`induction_with_natDegree_le`), as in Mathlib's `eval₂_reflect_mul_pow` for commutative
  targets.
- `isUnit_of_aeval_eq_zero` (`K` a field): if `g(a) = 0` and `g(0) ≠ 0`, then `a` is a unit,
  with inverse `-(g(0))⁻¹ (g.divX)(a)` (from `g = g.divX · X + g(0)`).
- `separable_reverse` (`K` a perfect field): if `g` is separable with `g(0) ≠ 0`, then
  `reverse g` is separable. Over a perfect field separable means squarefree. If
  `d² ∣ reverse g`, then `d(0) ≠ 0` because `reverse g` has nonzero constant term (the leading
  coefficient of `g`); `reverse` is multiplicative over a domain and `reverse (reverse g) = g`
  (the trailing degree of `g` is zero), so `(reverse d)² ∣ g`, `reverse d` is a unit, and
  `d` has degree `0`.

## Regular elements

Let `A` be a finite-dimensional central simple algebra over a field `K`.

- `minpoly_eq_reducedCharpoly_of_separable`: if the reduced characteristic polynomial `p` of
  `a` is separable, then `minpoly K a = p`. By reduced Cayley–Hamilton (`aeval_reducedCharpoly`)
  the minimal polynomial `q` divides `p`. Conversely the characteristic polynomial of left
  multiplication by `a` is `p ^ d` (`charpoly_leftMulMatrix_eq_reducedCharpoly_pow`), so over an
  algebraic closure every root of `p` is an eigenvalue of that matrix and hence a root of `q`;
  the roots of `p` are simple, so `p ∣ q`. This is the argument of the Library's
  `reducedCharpoly_eq_minpoly_of_separable` (module `Langlands.JacquetLanglands.RegularElliptic`)
  for division algebras, which uses no property of division algebras beyond these two facts.
- `eq_zero_of_sum_smul_pow_eq_zero`: if `p` is separable and
  `∑_{i < d} cᵢ aⁱ = 0` (`d` the reduced degree), then `c = 0`, from Mathlib's
  `linearIndependent_pow` and the previous result.
- `eq_zero_of_sum_smul_inv_pow_eq_zero`: the same for the powers of `u⁻¹` when `u` is a unit
  with separable reduced characteristic polynomial: multiplying `∑ cᵢ u⁻ⁱ` by `u^{d-1}` gives
  `∑ c_{d-1-j} uʲ`, and the previous result applies after reindexing by `Fin.rev`.

## Provenance

Internal. These are standard facts on regular semisimple elements, used for the conditions
"`f'(x)` is a unit" and "`1, x, …, x^{n-1}` are independent" in
`Langlands.CentralSimple.NumberFieldUnitaryRegularLocalStatement`.
