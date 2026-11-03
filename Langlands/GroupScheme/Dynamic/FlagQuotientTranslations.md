# Rational translations of an actual scheme quotient

Author: Worker 1275.

This internal construction starts with an actual morphism `π : G.X ⟶ Q` over
a field, a subgroup functor `H`, and the exact right-coset fiber equivalence on
every test scheme. It also assumes that the underlying scheme map of `π` is
an effective epimorphism. A quasi-compact flat surjective scheme morphism has
this property by the pinned Mathlib fpqc theorem.

Left multiplication by a rational group point preserves the fibers because
`(a * g)⁻¹ * (a * h) = g⁻¹ * h`. Arbitrary maps of underlying schemes having
equal quotient images determine maps over the same base, so the all-test fiber
criterion proves the relation required by `EffectiveEpi.desc`. Descent
constructs an actual scheme morphism `Q.left ⟶ Q.left`. Cancellation of `π`
proves that the result respects the base and that translations by a point and
its inverse are mutually inverse. Thus `flagQuotientTranslation` is an actual
relative-scheme isomorphism, with the proved compatibility
`π ≫ e.hom = L_a ≫ π`.

`localSections_of_rational_lifts` assumes actual surjectivity on the existing
`RingPoint` sets and one section on an actual open containing the entire image
of the identity coset. A lift of any rational quotient point supplies a rational
translation carrying the identity coset to that point. The published
identity-test and ring-test equivalence identifies the two conventions.
The section-transport construction then gives an actual algebraic section
on an open containing the entire image of the selected quotient point.

Provenance: elementary category and group laws together with effective-epimorphism
descent in the current Library and pinned Mathlib. Quotient existence, exact
fibers, the effective-epimorphism property, properness, rational-point lifting
and a section near the identity coset remain explicit geometric inputs or
separate obligations. This construction does not prove the full
`DynamicFlagQuotientExistenceStatement`.
