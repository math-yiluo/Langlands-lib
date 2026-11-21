# Derivatives of scalar evaluations on smooth unitary orbits

Differentiating the original inner product invariance gives skew symmetry
of each genuine real derivative on smooth vectors. Iterating that identity
moves a derivative word to a smooth test vector in the first argument of
the inner product.

The jointly smooth orbit family supplies norm smoothness of each genuine
word coordinate. To differentiate that coordinate on a translated orbit,
test against the dense smooth carrier. Move the word to the test vector
and use the ordinary genuine derivative of the original orbit. The dense
inner-product tests identify the resulting derivative in the original
Hilbert space. The argument uses only genuine orbit derivatives and is an
internal consequence of joint orbit smoothness and the Hilbert action.

A derivative-continuous scalar functional is a finite sum of Hilbert
pairings against those word coordinates. The sum is genuinely smooth in
the group variable. Differentiating it along right multiplication and
reapplying the pairing formula gives evaluation on the translated genuine
derived vector.

`SmoothFunctionalOrbitStatement` records smoothness and this differential
identity with the model, group and Hilbert universes free.
`smoothFunctionalOrbit` proves it.
