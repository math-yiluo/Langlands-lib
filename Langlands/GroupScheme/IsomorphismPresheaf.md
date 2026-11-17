# The presheaf of natural local group isomorphisms

This is an internal universal-property adapter for the full relative Isom
representability problem. It is derived from the published
`LocalGroupIso`, its refinement operation, and `GroupIsomorphismScheme`;
it is not a new claim from the literature.

`LocalGroupIso.presheaf G H` sends an arbitrary scheme over the base to the
type of natural local group-isomorphism families on that test. Restriction
is `LocalGroupIso.refine`. The identity and composition laws are checked
by equality of the evaluations on all relative tests. The value universe
is `u + 1`, since a family quantifies over all schemes in universe `u`.

`GroupIsomorphismScheme.representableBy` converts the existing universal
family and its bijections into a Mathlib `Functor.RepresentableBy`
record. Conversely, `ofRepresentableBy` evaluates a representation at
the identity of its parameter scheme to construct the universal family.
The naturality equation for the representation identifies restriction
of this family along each parameter point with the classification
equivalence at that point.

`nonempty_iff_representable` consequently identifies existence of the
supplied scheme interface with representation of this entire presheaf.
All tests are arbitrary relative schemes; no affineness or field-valued
restriction is imposed. This file supplies no geometric existence
theorem for a representing scheme.
