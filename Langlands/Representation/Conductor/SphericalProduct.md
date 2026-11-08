# The actual spherical denominator product

This internal unit applies the coordinate denominator polynomial from
`SphericalDenominator` to the actual lower-bounded model series from
`SphericalSeries`. It also supplies the algebraic step from a uniform upper
bound on all scalar specializations to finite support. The upper bound is an
explicit premise, and the scalar polynomial multiplier is unrestricted.

## Finite coefficient sums

For a commutative ring `A`, `finiteLaurentCoefficientSum S hS` is the finite sum
of the coefficients of a genuine Laurent series `S`, where `hS` proves that its
actual support is finite. `finiteLaurentSeries_eq_sum` reconstructs `S` as the
finite sum of the monomials `HahnSeries.single d (S.coeff d)` indexed by that
support. Its proof compares coefficient functions; each finite sum has at most
one nonzero summand at any given exponent. These constructions allow negative
exponents.

## Evaluation and bounds over the symmetric torus algebra

Let `σ` be a finite type and let `K` be an infinite field. The coefficient
algebra is the actual symmetric torus subalgebra from `TorusIdeal`; evaluation
uses every unit tuple `x : σ → Kˣ`.

`coordinateDenominatorPolynomial_coeff_zero` proves that `P.coeff 0 = 1`
implies the same normalization for the coordinate denominator polynomial.
It evaluates the denominator identity at zero and then applies separation by
unit-tuple evaluations.

`symmetricTorusLaurentSeries_eq_of_specializations` proves equality of two
Laurent series from equality after every unit-tuple specialization. The proof
applies the same separation theorem to each coefficient.
`symmetricTorusLaurentSeries_coeff_eq_zero_above` applies this argument to
vanishing above one common integer `B`. The bound must hold for all tuples and
all integer exponents greater than `B`. No inference from bounds that vary with
the tuple is made.

`symmetricTorusLaurentSeries_support_finite_of_specialized_upper_bound`
combines that common upper bound with a supplied coefficientwise lower bound
`d₀`. The actual support is contained in the finite integer interval
`[d₀, B]`, including when the interval is empty.

`symmetricTorusEvaluation_finiteLaurentCoefficientSum_scale` needs only a field,
without infinitude. If each coefficient of a finite-support series has
simultaneous-scaling degree equal to its integer Laurent exponent, it proves

```text
ev_(c*x) (sum_d S_d) = sum_d c^d * ev_x(S_d)
```

for every unit `c` and every unit tuple `x`. Here both sums run over the actual
finite support. The powers are integer powers in `K`; using a unit permits
negative degrees. The proof maps the finite sum through evaluation and uses
the imported scaling identity on each homogeneous coefficient.

## Product of the actual model series

In this section `F` is any nonarchimedean local field, with the topological and
measurable instances in the Lean signature. The hypotheses are an actual
`IsJacquetNormalization q ψ abv ϖ μ`, a smooth complex representation `π` of
`GL_(n+2)(F)`, a Whittaker functional `ℓ`, and a vector `w` in its coefficient
model. The field and representation universes are independent. No
irreducibility, admissibility or field-specific realization assumption is
introduced.

For any scalar polynomial `P : Polynomial ℂ`,
`corankOneModelDenominatorProduct` is defined to be

```text
corankOneModelLaurentSeries h π hπ ℓ w
  * finitePolynomialLaurentSeries
      (coordinateDenominatorPolynomial (Fin (n+1)) ℂ P).
```

This is an actual multiplication of genuine Laurent series over the symmetric
torus coefficient algebra. It does not assert that `P` is an L-polynomial or
that the product has finite support.

`corankOneModelDenominatorProduct_coeff` gives its coefficient at every integer
`d` as the finite convolution

```text
sum over m in the coordinate denominator's polynomial support:
  degreeCorankOneModelCoefficient h π hπ ℓ w (d - m)
    * coordinateDenominatorCoefficient (Fin (n+1)) ℂ P m.
```

The coefficient has simultaneous-scaling degree `d`, by
`corankOneModelDenominatorProduct_coeff_isHomogeneous`: the two factors in each
summand have degrees `d-m` and `m`, respectively. These are the actual integrated
coefficients and the actual localized homogeneous components of the coordinate
polynomial product.

`corankOneModelDenominatorProduct_coeff_eq_zero_below` gives an integer `d₀`
such that every product coefficient below `d₀` vanishes for every choice of
`P`. The previously proved lower bound for the model coefficients suffices
because the polynomial multiplier has only nonnegative exponents.

`corankOneModelDenominatorProduct_specialize` proves the exact formal identity

```text
map ev_x (model product)
  = specializedCorankOneModelLaurentSeries h π hπ ℓ w x
      * finitePolynomialLaurentSeries
          (product_i P.comp (C (x_i) * X)).
```

It uses coefficient-map compatibility of finite polynomial multiplication and
the polynomial specialization theorem from `SphericalDenominator`.
`corankOneModelDenominatorProduct_specialized_coeff` further identifies each
coefficient with a finite sum of actual scalar degree integrals, multiplied by
the evaluated denominator coefficients. The integral at degree `d-m` uses the
indicator of `sphericalQuotientDegree h.uniformizer t = d-m` and the corank-one
integrand at spectral parameter zero, exactly as in `SphericalSeries`.

Finally, `corankOneModelDenominatorProduct_support_finite` applies the algebraic
support theorem: if one integer `B` bounds above the support of every scalar
unit-tuple specialization of this product, then its actual support over the
symmetric torus algebra is finite. The lower bound is proved here from the
model data; the upper bound remains a premise.

## Provenance and remaining obligations

This is an internal deduction from the preceding spherical constructions,
finite sums and separation by evaluations. Its proof route explicitly
constructs the product, uses finite convolution, and applies separation
coefficient by coefficient. It makes the algebraic product and finite
coefficient-collection operations used in Jacquet's corrected argument
explicit; see *A correction to Conducteur des représentations du groupe
linéaire* (2012), Section 2, printed pages 520–521.

The functional equation and its resulting upper support bound are not proved
here. The module also does not prove L-polynomial existence or comparison,
analytic convergence, an essential-vector identity, uniqueness, or a conductor
theorem.
