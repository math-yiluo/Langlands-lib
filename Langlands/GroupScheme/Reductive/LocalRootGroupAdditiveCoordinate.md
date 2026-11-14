# Additive root-group coordinates over arbitrary local rings

This derived module applies the actual dynamic unipotent orbit construction
to the root-group coordinate algebra `coordU i mu nu`. Here the ambient group
is affine, `i` is a homomorphism from a finite coordinate split torus, and
`mu` and `nu` are its exponent cocharacters. The actual root group `Uc` is the
dynamic unipotent subgroup for `nu` inside the dynamic centralizer for `mu`.

`coordX_mul_of_homogeneous` says that a positive homogeneous algebra generator
of `coordU` is additive on points over every test scheme. It is the direct
specialization of `UnipotentPrimitive.appTop_mul` to `unipCochar i mu nu`, with
`coordX` the pullback of the same actual coordinate section. This statement
requires no smoothness, local-ring, reducedness or characteristic hypothesis.

If evaluation at this homogeneous coordinate is bijective,
`gaIsoUOfHomogeneous` constructs an isomorphism `Ga R ≅ Uc i mu nu`. It uses the
published `gaIsoU` construction with the additivity just proved: evaluation
at the polynomial coordinate is bijective on all algebra maps, the relative
Spec adjunction gives a natural bijection on all scheme points, and additivity
makes it a natural group isomorphism. `coordX_gaIsoUOfHomogeneous` records that
the chosen parameter pulls back the chosen coordinate to its original scalar.

`nonempty_gaIsoU_of_flat` assumes in addition a smooth affine ambient group
over a commutative local ring and the field-fibre hypotheses of
`exists_coordinate_of_flat`. These supply on every field fibre an isomorphism
from the additive group compatible with a torus character, whose pairing with
`nu` is the fixed positive natural degree. That published prerequisite gives
a homogeneous polynomial coordinate, so the construction above gives an
additive-group isomorphism over the original ring, including when it has
nilpotents.

The provenance is internal composition of `LocalRootGroupFlatCoordinate`,
`Dynamic.UnipotentPrimitiveCoordinate`, and the general all-test-scheme
parametrization in `LocalRootGroupParam`. No torus-equivariance over the
original ring, root parametrization in the sense of `IsRootParametrization`,
Weyl normalization or isomorphism theorem is asserted here.
