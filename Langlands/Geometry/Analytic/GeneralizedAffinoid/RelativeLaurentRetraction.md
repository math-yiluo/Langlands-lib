# Constant coefficient retraction for an arbitrary relative Laurent radius

Author: Worker 36.

This internal construction concerns a complete ultrametric normed field `K`,
an actual presented positive-polyradius affinoid algebra `A`, and any real
radius `t > 0`. The actual relative Laurent annulus `algebra K A t` is the
existing enlarged weighted Tate quotient, with the two new reciprocal radii
`t,t⁻¹` and equation `XY = 1`.

On relative restricted series with coefficients in `A`, the constant Laurent
coefficient is the sum of coefficients of monomials `XⁱYʲ` with `i = j`.
Every such monomial has weight exactly one. The weighted restricted-series
condition therefore makes this diagonal family summable, and its sum has norm
at most the weighted Gauss norm. This gives an additive continuous functional.
Its value on a monomial is its coefficient if the two exponents agree, and
zero otherwise.

Multiplication by `XY` shifts both exponents together and preserves their
difference. The functional consequently kills all multiples of `XY − 1`.
The proof checks monomials and extends the equality by the published
restricted-series monomial expansion and continuity. Its closed kernel then
contains the closed generated relation ideal.

`ConstantCoefficient.relative` descends this additive map to the actual
relative closed-equation quotient. Representatives with arbitrarily small
excess norm prove that the descended map is contractive. `retraction` composes
it with the existing contractive map from the enlarged scalar quotient to
the relative quotient.

`retraction_baseMap` proves that this map is a left inverse to the actual
structural map `baseMap K A t`. Contractivity of both maps yields `norm_baseMap`
and `isometry_baseMap`: adjoining this reciprocal-radius Laurent variable
preserves the original algebra norm exactly.

The derivation uses the existing relative-series comparison, the actual
quotient norms and the general monomial-expansion helper in
`RelativeUnitAnnulusNormalFormProof`. It introduces no new original-literature
assertion. Unlike a multiplicative retraction, constant Laurent coefficient
is only additive. It requires no independent-radius condition, nontrivial
valuation, strict presentation, reducedness, nonzero quotient, or nonempty
spectrum. Bounded descent along finite covers and unrestricted atlas
restriction maps remain separate constructions.
