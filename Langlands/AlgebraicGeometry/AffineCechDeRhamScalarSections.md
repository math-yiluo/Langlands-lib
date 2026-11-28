# Scalar extension of affine section rings

For a scheme over the spectrum of a commutative ring `R` and a commutative
`R`-algebra `T`, take the actual Cartesian pullback over `Spec T`. The map on
sections along the projection to the original scheme commutes with the
base algebra maps on all opens where the pullback is defined.

For an affine open of the original scheme, `isPushout_scalarSections`
identifies the ring square of the inverse-image open as a pushout. This is
the affine section comparison for a Cartesian square, with the base rings
identified with their global functions. The tensor pushout gives
`scalarSectionEquiv` over `T`. On `t ⊗ a` it gives the pullback of `a`
multiplied by `t`. The presentation allows an open specified by equality
with the inverse image, as occurs for tuple intersections of affine covers.
