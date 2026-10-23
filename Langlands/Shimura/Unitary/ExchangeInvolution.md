# Similitudes of an exchange involution

This module supplies an internal algebraic prerequisite for splitting the
Harris group over complex coefficient algebras. It constructs the
similitude group of an exchange involution explicitly from a free algebra
unit and a scalar unit. It assumes only a commutative ring `R`, an
`R`-algebra `A` whose ring may be noncommutative, and an actual
`AlgebraInvolution R A` called `σ`.

## The involution and the inverse construction

`σ.exchange` is the `R`-algebra involution on `A × A` defined by

\[
 (a,b)\longmapsto (\sigma(b),\sigma(a)).
\]

Its linearity, preservation of one, reversal of products, and involutivity
are proved componentwise from the corresponding properties of `σ`.
`exchange_apply` gives this formula. `exchange_units` gives the analogous
formula on units, expressed through the standard equivalence
`MulEquiv.prodUnits : (A × A)ˣ ≃* Aˣ × Aˣ`.

For `c : Rˣ`, `scalarUnits c` is its existing image in `Aˣ`.
`units_scalarUnits` proves that `σ.units` fixes it because the algebra
involution fixes the scalar embedding. No injectivity of that embedding
is needed.

Given `(a,c) : Aˣ × Rˣ`, `σ.exchangeLift` constructs the unit of `A × A`
whose component pair is

\[
 (a,\ c\,\sigma(a)^{-1}).
\]

Here `c` in the second component means `scalarUnits c`. The Lean
expression is `scalarUnits c * σ.inverseUnits a`, where `inverseUnits`
is the existing group automorphism obtained by combining the involution
with inversion. The lift is a monoid homomorphism, built from the first
projection, the existing `similitudeCompanion`, and
`MulEquiv.prodUnits.symm`. The theorem `exchangeLift_components` gives its
component formula.

`exchangeLift_mem` proves that the lift with recorded multiplier `c`
belongs to `σ.exchange.similitudes`. It uses the defining units equation
for similitudes, applies the product-units equivalence, and checks both
components. The identities that the involution fixes scalar units and is
involutive reduce those equations to cancellation in the unit group.

## The group equivalence

`σ.exchangeSimilitudesEquiv` is a multiplicative equivalence

\[
 \operatorname{GU}(A\times A,\sigma_{\mathrm{exchange}})
 \simeq A^\times\times R^\times.
\]

The group on the left is exactly the existing subgroup of
`(A × A)ˣ × Rˣ` defined by the equation `g σ_exchange(g) = c`.
The forward map retains the first component of the algebra unit and the
recorded scalar multiplier. The inverse sends `(a,c)` to the constructed
exchange lift with that multiplier.

For the left inverse proof, the second component of the similitude
equation is `b * σ(a) = c`. Cancellation gives
`b = c * σ(a)⁻¹`, proving that the lift recovers the omitted component.
The right inverse follows directly from the lift formula. Preservation
of multiplication follows from the product-units equivalence and the two
projections. Thus no choice, uniqueness assumption on the multiplier, or
existence assumption about a missing second unit is used.

The projection theorems `exchangeSimilitudesEquiv_fst` and
`exchangeSimilitudesEquiv_snd` identify the first unit and the multiplier.
`exchangeSimilitudesEquiv_symm_components` records both components of the
inverse explicitly.

## Provenance and scope

These are consequences of the established algebra-involution and
similitude definitions in `Involution`, `Similitude`, and
`InvolutionBaseChangeTower`, together with the standard product-units
equivalence. This is an internal construction rather than a translation
of an additional external theorem. The hypotheses allow arbitrary
commutative coefficient rings, including nonreduced rings, and do not
require the algebra or scalar embedding to be faithful or nontrivial.

To obtain the Harris splitting, subsequent work must identify its
coefficient-ring matrix involution with such an exchange involution,
apply this equivalence to the matrix algebra at all real places, and
prove the required naturality and scheme comparison. This module alone
does not construct a scheme isomorphism, smoothness or reductivity, or
complete the Harris PEL geometry and coefficient descent.
