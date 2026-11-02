# Finite gluing in the stored algebra of a full affinoid domain

Author: Worker 36.

This internal derivation concerns a finite full-domain cover `c` of a full
represented domain `U` over an actual presented positive-polyradius affinoid
algebra `A`, over any complete ultrametric normed field `K`.

`algebra_ext_of_restrict_eq` proves that the original actual bounded restrictions
detect equality of elements in `U.algebra`. Its proof refines `c` by rational
charts over that stored algebra and applies the uniqueness part of the published
whole-spectrum rational gluing theorem.

`AlgebraCompatible` requires a family of elements in the original component
algebras to agree after any actual represented-domain test mapping to two
components. `algebraRestrict` uses the original stored bounded restrictions.
Restrictions of a global element are compatible by uniqueness of actual domain
arrows over `A`.

For any relative rational refinement, `algebraFamily` restricts the original
elements through its chosen component maps. `algebraFamily_compatible` checks
the rational intersection equations using the extended actual intersection
domain and its two bounded projections. The published whole-spectrum rational
gluing theorem then constructs an element of `U.algebra`.
`restrict_eq_of_refined_eq` verifies its value on every original component:
pull the refining rational charts back to that component algebra, use their
whole-spectrum coverage, and compare the two restrictions on the actual rational
intersections. Rational separation identifies the two component elements.

`algebra_existsUnique` packages this existence and uniqueness.
`algebraGlue` chooses the resulting element, and the two inverse equations
construct `algebraGluingEquiv` between the stored algebra's elements and the
full-test-compatible local families.

The construction derives from full-domain localization, relative rational
refinement, actual rational intersections and whole-spectrum rational gluing.
It invokes no additional original-source assertion or private peer draft.
Arbitrary positive radii, trivial valuations, nilpotents, zero quotient algebras,
and empty spectra or covers remain allowed. This file proves finite element
descent; the categorical stored-algebra sheaf property is a separate construction.
