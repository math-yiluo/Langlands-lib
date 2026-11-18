# Ambient unramified twists in valuation-kernel product coordinates

This derived unit connects the integral product coordinates from
`RationalValuationKernelCoordinates` with actual unramified parameters and
their established translations on regular functions and the function field.
The schemes are affine and locally of finite type over a nonarchimedean
local field, and their rational points have the canonical point topologies.
The complement parameters use a supplied integral product chart. Extending
them to ambient unramified characters uses the hypothesis that the first
block is the kernel of the actual ambient valuation map.

For any tuple of nonzero complex numbers on the second block,
`complementImageCharacter` evaluates the corresponding Laurent monomial on the
actual valuation image. `complementParameter` reconstructs its actual
unramified character. Its restriction to the valuation kernel is trivial.
The proved kernel characterization of ambient restriction therefore gives
`complementParameter_ambient`: this parameter is the restriction of an ambient
unramified character.

`productLaurentAlgebraEquiv` transports the group algebra along the supplied
integral lattice equivalence and then uses the existing actual regular scalar
algebra equivalence.
`productRegularScaling` conjugates actual parameter translation by this map.
`productRegularScaling_single` proves that a monomial with exponent pair
`(m₁,m₂)` is multiplied by the product of the second-block coordinates raised
to `m₂`; the first exponent block is unchanged.

For a connected reductive source scheme, `productFunctionFieldEquiv` extends
the same algebra equivalence to the actual scalar function field.
`productFractionScaling` is the corresponding conjugate of actual scalar
translation; `productFractionScaling_algebraMap` and
`productFractionScaling_single` verify its exact action on embedded regular
functions and monomials. `productFractionScaling_fixed_of_ambient_fixed` shows that an
actual fraction fixed under all ambient unramified restrictions becomes fixed
under every second-block scaling. The lemma is general in the fraction; the
actual opposite canonical scalar has its ambient invariance proved separately
in `DynamicOppositeAmbientTwist`.
