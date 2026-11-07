# Polynomial descent under truncated translations

This is derived content by Worker 1369. It uses Mathlib's multivariate
polynomial evaluation, expansion, partial derivatives and support ideals,
together with the published derivative criterion
`GradedHopf.exists_expand_of_pderiv_eq_zero` from
`Langlands.Algebra.GradedHopf.PolynomialFrobenius`. No new assertion from an
external source is assumed.

For any variable type `σ` and commutative coefficient ring `R`,
`translation` is the ring homomorphism

`R[X_i] → R[X_i][T_i]`, with `X_i ↦ X_i + T_i`.

The inner variables are the base variables, and the outer variables are
translation parameters. Constants map to nested constants.
`translationAlgebra` equips the same map with its algebra structure over
`R`; its compatibility uses the scalar tower through the inner polynomial
ring. The constant coefficient of `translation F` is `F`. Partial
 differentiation in an outer variable commutes with translation, and the
coefficient of `T_i` is the inner partial derivative `pderiv i F`.
These identities are proved by polynomial induction and coefficient
comparison.

`doubleExpansion q` expands both sets of variables by the factor `q`.
Its coefficient at `q • m`, for nonzero `q`, is `expand q` of the original
coefficient at `m`. If `p` is the exponential characteristic of `R`, the
characteristic-power sum identity gives

`translation (expand (p^r) H) - C (expand (p^r) H)`
`= doubleExpansion (p^r) (translation H - C H)`.

Here `expand q` substitutes `X_i^q` for `X_i` while leaving coefficients
unchanged. The results therefore concern powers of variables; they do
not require coefficients to have roots in the base field.

`TruncatedInvariant q F` says that every coefficient of
`translation F - C F` at an outer monomial `m` with `m i < q` for every
`i` vanishes. `truncationIdeal q` is the support ideal consisting of
polynomials whose nonzero monomials have some exponent at least `q`.
Its membership criterion is precisely vanishing of the complementary
strict-box coefficients. Every `X_i^q` belongs to this ideal, including
when `q = 0`. The subtraction in the translation condition makes its
coefficient at zero vanish automatically.

Over any field `k`, for any exponential characteristic `p` and height
`r : ℕ`, `truncatedInvariant_iff_exists_expand` proves

`TruncatedInvariant (p^r) F ↔ ∃ H, F = expand (p^r) H`.

The forward proof separates exponential characteristic one from the
prime case. In the prime case it inducts on `r`. At positive height,
the single-variable linear translation coefficients force all partial
derivatives to vanish. The published derivative criterion gives
`F = expand p H`. Comparing the coefficients at `p • m` in the double
expansion reduces truncated invariance to height `r` for `H`.
Injectivity of `expand p` permits this reduction, and multiplication
of expansion factors finishes the induction. For the reverse direction,
a nonzero strict-box exponent has a coordinate not divisible by
`p^r`, so its coefficient in the outer expansion vanishes; the exponent
zero was already handled. This proof works for an arbitrary variable
type, with no finiteness assumption.

`UniversalPowerInvariant q F` quantifies over every commutative
`k`-algebra `A : Type (max u v)` and every pair of algebra maps from
`k[X_i]` to `A`. If the `q`-th powers of their values agree on every
polynomial, their values on `F` must agree.
`universalPowerInvariant_iff_exists_expand` proves that, for `q = p^r`,
this condition is also equivalent to `F = expand (p^r) H` for some `H`.

To obtain truncated invariance from this pointwise condition, the proof
takes the nested polynomial ring modulo its outer `truncationIdeal` as
one of the coefficient algebras. The two algebra maps are universal
translation and constant inclusion followed by the quotient map. Their
powered values agree: before taking the quotient, postcomposition of
the iterated Frobenius with either map agrees on constants and variables,
since the outer variable powers vanish in the quotient. The universal
condition now identifies the two values of `F`, and the quotient kernel
criterion gives truncated invariance. This argument uses exponential
characteristic only in the nested polynomial ring; it does not require
a nontrivial quotient algebra. In the reverse direction, algebra-map
extensionality on constants and variables shows that power-congruent
maps agree after `expand q`, for any natural `q`.

Both characterizations include height zero, exponential characteristic
one, and an empty or infinite variable type. The universal condition
allows nonreduced and zero coefficient algebras. This unit supplies the
polynomial descent step. It does not identify actual group-coordinate
invariants with this condition, exclude the covariant kernel vector,
prove fixed-height restriction injectivity, or prove the whole-space
Steinberg dimension bound or `SteinbergBigCellStatement`.
