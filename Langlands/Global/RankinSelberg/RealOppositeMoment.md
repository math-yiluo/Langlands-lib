# Compact-finite sections with arbitrary moments on the real opposite cell

## Polynomials and sections

* `minorPoly n k` is the bottom-right minor on the rows and columns `≥ k` of the matrix of
  coordinate variables, and `momentPoly n = Π_{k<n} (minorPoly n k)²`.
* `signPoly ds n = Π_l X(l,l)^{ε_l}`, where `ε_l` is a natural number with
  `realPositionCharacter ds l (-1) = (-1)^{ε_l}`, chosen (by `Classical.choose`) from the
  existence statement `RealStrictCharacterLanglandsQuotient.exists_signs`. Only this property
  of the exponents is used.
* `momentSection n ds m` is the Library's Gram section
  `RealGramFunction.gramFunction s (signPoly ds n · momentPoly n ^ m)`, with `s` the shifted
  position exponents of `ds`.

`momentPoly` is even in each row (`momentPoly_parity`), and `signPoly` has the sign parity of
the characters (`signPoly_parity`), so the Gram section lies in the principal series of `ds`
(`momentSection_mem_principalSeries`). For a real character list `cs.map RealBlock.character`,
`momentSection_mem` shows that it is a vector of the `O(n)`-finite standard module
`Automorphic.realStandardKFinite`. At the identity every minor and the sign monomial take the
value one, so `momentSection_one` gives the value `1`. The sections are smooth and continuous
(`contMDiff_momentSection`, `continuous_momentSection'`).

## Behaviour on the opposite cell

`orthogonalEval_momentPoly_transpose`: on the signed orthogonal Iwasawa part of `uᵀ`
(`u` upper unipotent), `momentPoly` evaluates to the inverse of the Gram product
`oppositeGramProduct u` of `RealOppositeGramBound`. Indeed write `uᵀ = a v κ` with `a`
diagonal, `v` upper unipotent and `κ` orthogonal; the bottom-right minors of `κ` are those of
`v⁻¹ a⁻¹ uᵀ`, and the squared minor on the rows `≥ k` equals the inverse of the tail Gram
determinant of `uᵀ` (padded minors multiply along upper triangular factors,
`padded_mul_of_upper`). Hence (`momentSection_add_opposite`)

`momentSection n ds (m + j) (uᵀ) = momentSection n ds m (uᵀ) · (oppositeGramProduct u)^{-j}`.

## Moments

`norm_upperEntries`: the supremum norm of the upper entry vector of `u` is the entrywise
norm `‖u - 1‖`. `realMatrixHeight_transpose_le` bounds the Library's matrix height of `uᵀ`
by `C (1 + t)^{2(r+2)}` whenever all entries of `u` are bounded by `1 + t`
(from `realMatrixHeight_mul_absDet_sq_bound`, since `det uᵀ = 1`).

`RealOppositeMomentStatement`: for every rank `r + 1`, block list `ds` and order `L` there is
`m₀` such that for all `m ≥ m₀`

`u ↦ (1 + ‖u - 1‖)^L · momentSection (r + 1) ds m (uᵀ)`

is integrable for `realEntryLebesgue (r + 1)`. `realOppositeMoment` proves it: the Library's
polynomial height bound for principal-series sections (`realPrincipalSeriesHeight`) bounds
`momentSection … 0 (uᵀ)` by a power `R^E` of `R = oppositeGramProduct u` (using
`1 + ‖u - 1‖ ≤ 2R` from `realOppositeGramBound`), and the factor `R^{-j}` for
`j ≥ E + L + p` leaves a bound `K (1 + ‖u - 1‖²)^{-p}`, which is integrable in the entry
coordinates once `2p` exceeds their dimension (`integrable_rpow_neg_one_add_norm_sq`).

This module is the real counterpart of the Library's `ComplexOppositeMoment`. Its vectors give
the weighted integrability used in `RealOppositeNonzero`, which produces a compact-finite vector
with nonzero unweighted opposite-cell mass; that mass normalizes the compact averages of
`RealNormalizedCompactAverage`.
