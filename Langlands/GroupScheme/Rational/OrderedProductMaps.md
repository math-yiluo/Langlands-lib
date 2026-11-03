# Factor maps and monomorphisms for actual ordered multiplication

This internal categorical module continues `Rational.OrderedProductPoints`.
It keeps the actual finite product and actual ordered scheme multiplication
over an arbitrary base scheme. No geometric or weight hypothesis is used.

`productFactorMap` is the underlying scheme morphism of the categorical
product of a family of group-scheme homomorphisms. Its projection formula
comes from the universal product map in the category of group objects.
The coordinate and inverse-coordinate formulas follow by applying those
projections to points. The finite index universe remains independent of
the base-scheme universe.

`orderedMultiplication_map` proves the commuting square of actual scheme
morphisms induced by commuting factor and ambient group homomorphisms.
It evaluates the left side in finite coordinates and uses the established
`orderedPoints_map` identity.

`mono_orderedMultiplication_iff` identifies monomorphy of the actual scheme
map with injectivity of ordered factorization on every test scheme. In one
direction it cancels the multiplication map after reassembling the
coordinate families. In the other direction injectivity of coordinates
reduces cancellation to the stated pointwise injectivity. This supplies the
monomorphism input used by descent arguments, without claiming that any
particular family satisfies it.

The empty and singleton formulas evaluate the original list definitions.
The empty-case isomorphism criterion says that ordered multiplication is an
isomorphism exactly when every test-point group of its target is a
subsingleton. It uses the bijectivity criterion from `OrderedProductPoints`;
it does not derive target triviality from an empty Lie weight support.

All claims are derived from product universal properties, actual point
group laws, and categorical cancellation. The intended use is the
central-extension argument for the exact CGP ordered-product target, but
this module asserts no realization, cross-exclusion, or geometric descent
theorem.
