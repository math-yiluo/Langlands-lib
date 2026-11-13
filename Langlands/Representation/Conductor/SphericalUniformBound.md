# Uniform upper degree bounds from pointwise ones

This internal module supplies one step of Jacquet's corrected existence proof of the
essential vector (Jacquet 2012, section 2, printed pages 519-522). There a Laurent
series with symmetric Laurent polynomial coefficients is shown to have finite support
after multiplication by `∏ P(X x_i)`. The input available for each fixed tuple `x` is
only a pointwise statement: after specializing at `x` the product is a Laurent
polynomial, with a degree bound that may depend on `x`. This module proves that such
pointwise bounds always give one bound for all `x`. The argument is the Baire category
theorem on `ℂ^σ`. Jacquet instead obtains the uniform bound from the JPSS functional
equation; this module does not use it.

## Results

- `mvPolynomial_eq_zero_of_eval_eq_zero_on_open`: a complex polynomial in finitely many
  variables that vanishes on a nonempty open subset of `ℂ^σ` is zero. The open set
  contains a product of open balls, each infinite, and Mathlib's
  `MvPolynomial.funext_set` applies.
- `torusPolynomial_exists_numerator`: for a Laurent polynomial `p` in the published
  coordinate ring `TorusPolynomialAlgebra σ ℂ`, there are `m` and a polynomial `a`
  with `p(x) (∏ x_i)^m = a(x)` at every tuple of units `x`. If `a = 0` then `p = 0`.
  This is the localization equation `p · (∏ X_i)^m = a`, evaluated, together with the
  fact that `∏ X_i` is a unit.
- `torusPolynomial_exists_upper_bound` (the main result): let `c : ℤ → TorusPolynomialAlgebra σ ℂ`.
  Suppose that for every tuple of units `x` there is `B` with `c_d(x) = 0` for all
  `d > B`. Then there is one `B` with `c_d = 0` for all `d > B`.

  Proof. Choose numerators `a_d` of the `c_d` as above. Index closed subsets of `ℂ^σ`
  by `σ ⊕ ℤ`: the coordinate hyperplane `{z_i = 0}` for `i ∈ σ`, and the common zero set
  of the `a_d`, `d > B`, for `B ∈ ℤ`. Both kinds are closed, because polynomial
  evaluation is continuous. Together they cover `ℂ^σ`. A point with a zero coordinate
  lies on a hyperplane. Any other point is a tuple of units `x`, and the hypothesis at
  `x` puts it in the set indexed by its bound `B`. The index type is countable, so by
  the Baire category theorem (`nonempty_interior_of_iUnion_of_closed`) one of these
  sets has nonempty interior. It cannot be a hyperplane: the polynomial `X_i` would then
  vanish on an open set, hence be zero. So it is the set indexed by some `B`. Every
  `a_d` with `d > B` vanishes on its interior, so `a_d = 0`, hence `c_d = 0`.
- `symmetricTorusLaurentSeries_exists_upper_bound`: the same statement for a Laurent
  series `S` over the published `symmetricTorusSubalgebra σ ℂ` and its specializations
  `S.map (symmetricTorusEvaluation σ ℂ x)`. The conclusion is one bound `B` that works
  for every specialization.
- `corankOneModelDenominatorProduct_support_finite_of_pointwise`: for the published
  actual model denominator product `corankOneModelDenominatorProduct h π hπ ℓ w P`, if
  each of its specializations at a tuple of units vanishes beyond some degree depending
  on the tuple, then the product has finite support over the symmetric Laurent algebra.
  This combines the previous result with the published
  `corankOneModelDenominatorProduct_support_finite`, which needs a uniform bound and
  supplies the lower bound itself.

No hypothesis on `π` beyond those of the published product (smoothness `hπ` and
Jacquet's normalizations `h`) is used.
