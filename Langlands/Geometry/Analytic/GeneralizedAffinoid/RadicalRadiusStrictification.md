# Strict presentations for radical-value-group radii

This internal supporting construction works over every complete ultrametric
normed field `K : Type u`. If each radius of an actual finite presentation
`A : PresentedAffinoidAlgebra K` has a positive integral power equal to a scalar
norm, it constructs an actual strict presentation over the same field and a
bounded algebra equivalence with `A`. The equivalence and both of its bounds are
constructed explicitly. The original quotient may be zero or nonreduced, and
its coordinate tuple may be empty. No nontrivial valuation is required.

The entry construction is `RadicalStrictification.boundedEquiv`; the existential
form is `RadicalStrictification.exists_strictPresentation`. All declarations
except the general power lemma are in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.RadicalStrictification`.

`RadiusData K r` stores scalars `a_i` and positive natural exponents `n_i` with
`||a_i|| = r_i ^ n_i`. The scalars are nonzero because the radii are positive.
`radiusDataOfRadical` chooses this data from the published
`RadiusInRadicalValueGroup` condition.

For each original coordinate `x_i`, choose `b_i = 1` when `r_i <= 1` and
`b_i = a_i` otherwise. Then `r_i <= ||b_i||`, and `b_i` is nonzero. Form the
finite tuple consisting of

- `b_i^{-1} x_i`, and
- `a_i^{-1} x_i ^ n_i`.

Both kinds of coordinates have norm at most one. The needed estimate
`||x_i ^ m|| <= r_i ^ m` comes from applying the contractive presentation map
to powers of the weighted Tate coordinate; it does not require the quotient
unit to have norm one. The tuple has uniformly bounded monomials by the finite
tuple power criterion. Its zeroth power is handled separately by the quotient
unit estimate, including for the zero algebra.

`evaluation` is the actual bounded strict Tate evaluation at this tuple.
`presentation` is the strict Tate algebra on twice the original arity, divided
by the whole kernel of that evaluation. The kernel is closed by continuity.
`fromPresentation` is the bounded map `e : Q -> A` obtained by closed-ideal
quotient descent. It is injective by the algebraic kernel-quotient argument:
equal images of representative series imply that their difference belongs to
the defining ideal. At this stage surjectivity is not assumed.

Write `W_i` and `S_i` for the strict coordinate classes in `Q`, and put
`y_i = b_i W_i`. Their images under `e` are the original `x_i`. Injectivity of
`e` proves the exact identity `y_i ^ n_i = a_i S_i`, since both sides map to
`x_i ^ n_i`. Every power of `S_i` has norm at most one, by applying the
contractive strict presentation map to the corresponding source coordinate
power. Thus `y_i ^ n_i` has bounded powers weighted by `r_i ^ n_i`.

The general lemma `Langlands.Analytic.HasRadiusBoundedPowers.of_pow` recovers an
`r`-weighted power bound for `y` from an `r^n`-weighted bound for `y^n`, when
`r > 0` and `n > 0`. Its implemented proof writes each exponent as
`n * (m / n) + m % n` and bounds the finitely many residual powers by
`1 + sum_{j < n} ||y^j|| / r^j`. It uses submultiplicativity and includes the
zeroth power. It is valid in any normed ring.

The finite weighted monomial criterion now produces `weightedEvaluation`, an
actual bounded map from the original weighted Tate algebra into `Q`, sending
each original coordinate to `y_i`. Coordinate uniqueness proves that composing
with `e` is the original presentation map. Since `e` is injective, this weighted
evaluation annihilates the original ideal. `toPresentation` descends it to a
bounded map `f : A -> Q` through that closed ideal. Quotient surjectivity proves
`e(f(a)) = a`. Injectivity of `e` then proves `f(e(q)) = q`.
`BoundedAlgEquiv.ofHomInv` packages exactly these maps and bounds.

This is a derived internal construction from strict and weighted Tate
evaluation, finite monomial criteria, quotient descent, and the existing
radical-value-group predicate. It does not invoke an open mapping theorem,
series division, a nonzero quotient hypothesis, or an algebraic extension of
the coefficient field. The resulting equivalence is bounded in both directions;
no equality of quotient norms is claimed.

This unit is conditional on the displayed radical-value-group witnesses. It
does not construct a common Laurent extension for a domain and its ambient
algebra, transport full domain representation to strict presentations, or prove
`Domain.FiniteRationalCoverStatement`. Those remain separate host obligations.
