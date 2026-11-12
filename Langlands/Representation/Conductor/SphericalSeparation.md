# Separation by the spherical Laurent coefficients

This internal unit proves a separation result for the uniqueness clause of Jacquet
2012, Theorem 1 (printed page 517). That clause says the essential vector of a generic
representation of `GL_(n+2)` is unique once one also requires
restriction invariance; Jacquet attributes it to Jacquet, Piatetski-Shapiro and
Shalika 1981.

Fix Jacquet's normalizations `h : IsJacquetNormalization q ψ abv ϖ μ`, a smooth
representation `π` of `GL_(n+2)(F)` over an arbitrary nonarchimedean local field `F`,
a Whittaker functional `ℓ` and a vector `w` of its Whittaker model. Assume `w` is
right `GL_(n+1)(O)`-invariant on `diag(GL_(n+1), 1)`
(`IsIntegralInvariantOnRestriction π ℓ w`). If every Laurent degree coefficient
`degreeCorankOneModelCoefficient h π hπ ℓ w d` vanishes, then
`w(diag(g, 1)) = 0` for every `g ∈ GL_(n+1)(F)`. These coefficients come from
`Conductor/SphericalSeries`; they are the degree-`d` parts of the corank-one integral
of `w` against the spherical Whittaker functions.

The unit has internal provenance. It does not assert the essential identity, or the
existence or uniqueness of the essential vector. Two further steps toward uniqueness
are not part of this unit: relating these coefficients to the corank-one integrals
of the essential identity, and recovering `w` from its restriction to
`diag(GL_(n+1), 1)`.

## Iwasawa cells

- `quotientExponent hϖ t` is the Iwasawa exponent `lam` of `g = u ϖ^lam k`
  (`exponent hϖ g`), descended to the quotient `N_(n+1) \ GL_(n+1)`
  (`LeftUnipotentQuotient n F`). `sphericalQuotientDegree_eq_sum` identifies the
  Library's `sphericalQuotientDegree` with the sum of its entries.
- `sphericalCell hϖ lam` is the fibre of `quotientExponent` over `lam`.
  `sphericalCell_eq_image` shows that it is the image of `ϖ^lam GL_(n+1)(O)` in the
  quotient. Hence each cell is nonempty (`sphericalCell_nonempty`), open
  (`isOpen_sphericalCell`) and compact (`isCompact_sphericalCell`).
- `sphericalCell_measure`: every cell has positive finite mass for the
  Jacquet-normalized measure `μ`. This is `IsCompatible.measure_pos_lt_top` applied
  to `h.measure`.

## The degree coefficients as finite sums

- `cellCorankOneValue h π ℓ w lam` is the Laurent-valued corank-one function
  `corankOnePolynomialFunction` of `w` at `ϖ^lam`:
  `w(diag(ϖ^lam, 1)) · |det ϖ^lam|^(-1/2) · W(ϖ^lam; X; ψ̄)`.
- `corankOnePolynomialFunction_mul_integral`: under restriction invariance this
  function is right `GL_(n+1)(O)`-invariant. Each of its three factors is invariant.
  The `w` factor is invariant by hypothesis, `|det|` because `abv` is trivial on
  units, and the spherical factor by `sphericalWhittakerPolynomial_mul_integral`.
- `corankOnePolynomialIntegrand_eq_cellValue`: the Laurent-valued integrand on the
  quotient equals `cellCorankOneValue` at the exponent of the point. It is
  therefore constant on each cell.
- `cellCorankOneValue_of_antitone`: for dominant (antitone) `lam` the value is
  `(w(diag(ϖ^lam, 1)) · |det ϖ^lam|^(-1/2) · halfModulus q lam) • symmetricTorusSchur ℂ lam`.
  `cellCorankOneValue_of_not_antitone`: for non-dominant `lam` the value is `0`.
  Both follow from `sphericalWhittakerPolynomial_torus`.
- `degreeCorankOneModelIntegrand_eq_sum`: let `b` bound below every exponent at
  which the Laurent-valued function is nonzero. The Library's
  `model_corankOne_polynomial_exponents_lower_bound` provides such a `b`. Then the
  degree-`d` integrand is the finite sum, over `lam` in
  `boundedDegreeExponents (n + 1) b d`, of the indicator of `sphericalCell lam`
  times `cellCorankOneValue lam`.
- `degreeCorankOneModelCoefficient_eq_sum`: under the same hypothesis,
  `degreeCorankOneModelCoefficient h π hπ ℓ w d` equals
  `∑ lam ∈ boundedDegreeExponents (n + 1) b d, μ.real (sphericalCell lam) • cellCorankOneValue lam`.
  The proof evaluates both sides at every tuple `x` of Satake parameters
  (`symmetricTorus_eq_of_evaluations`). The left side is the scalar degree integral
  (`symmetricTorusEvaluation_degreeCorankOneModelCoefficient`). It is the integral
  of a finite sum of constants on cells of finite mass, computed by
  `integral_finsetSum` and `integral_indicator_const`.

## Vanishing

- `IsJacquetNormalization.residueCardinality_ne_zero`: `q ≠ 0`, since
  `abv ϖ = q⁻¹` and `ϖ ≠ 0`. Consequently `halfModulus_ne_zero`: the
  half-modulus factor never vanishes.
- `torus_eq_zero_of_antitone_of_degreeCoefficients_eq_zero`: assume all degree
  coefficients vanish and let `lam` be dominant. Suppose
  `w(diag(ϖ^lam, 1)) ≠ 0`, and put `d = ∑ i, lam i`. The degree-`d` coefficient
  formula gives a vanishing linear combination of the Schur expressions
  `symmetricTorusSchur ℂ ν`, over the dominant `ν` of degree `d` above `b`. Its
  coefficients are `μ.real (sphericalCell ν) · w(diag(ϖ^ν, 1)) · |det ϖ^ν|^(-1/2) ·
  halfModulus q ν`. The weight `lam` occurs in this combination: its cell value is
  nonzero, so `b ≤ lam i` for every `i`. Linear independence
  (`symmetricTorusSchur_linearIndependent`, from `Conductor/SchurIndependence`)
  makes its coefficient zero. This contradicts the positivity of the cell mass and
  the nonvanishing of the other factors.
- `torus_eq_zero_of_not_antitone_of_restriction`: for non-dominant `lam`,
  `w(diag(ϖ^lam, 1)) = 0` without any coefficient hypothesis. The function
  `g ↦ w(diag(g, 1))` is equivariant for the standard character of `N_(n+1)`
  (`corankOne_standardCharacter`) and right `GL_(n+1)(O)`-invariant. Because `ψ` has
  conductor `O`, there is `y ∈ O` with `ψ(ϖ⁻¹ y) ≠ 1`. So the standard character
  is nontrivial on `1 + ϖ⁻¹ y E_(i,i+1)` for every `i`, and the Library's
  `UnramifiedWhittaker.eval_torus_eq_zero_of_not_antitone` applies.
  `standardCharacter_adjacentUnit_val` computes the standard character on these
  elementary matrices.
- `eq_zero_on_restriction_of_degreeCoefficients_eq_zero` (main result): write
  `g = u ϖ^lam k` (`exists_eq_exponent`). Then
  `w(diag(g, 1)) = ψ_N(u) · w(diag(ϖ^lam, 1)) = 0` by the two previous results.
- `eq_zero_on_restriction_of_corankOneModelLaurentSeries_eq_zero`: the same
  conclusion from `corankOneModelLaurentSeries h π hπ ℓ w = 0`, whose coefficients
  are the degree coefficients.
