# Normalized cocycle extensions

For a group `G` acting by automorphisms on a commutative group `A`,
`Langlands.NormalizedTwoCocycle G A` contains an actual function on `G × G`,
Mathlib's multiplicative two-cocycle identity, and normalization at `(1,1)`.
The groups may live in independent universes. The axis identities and
inverse-pair identity are proved from the cocycle equation.

The extension has the actual carrier of pairs `(a,g)`, with its own group
structure:

`(a,g) * (b,h) = (a * (g • b) * c(g,h), g*h)`.

The identity is `(1,1)` and the inverse is
`((g⁻¹ • a⁻¹) * c(g⁻¹,g)⁻¹, g⁻¹)`. Associativity follows by expanding
the action and applying the cocycle identity; normalization gives the
identity laws and the inverse formula gives cancellation.
The coefficient inclusion is injective, the projection is surjective,
and the image of the inclusion equals the kernel of the projection.
The distinguished section is a map of sets. Its multiplicative defect is
exactly the given cocycle. Conjugation on the coefficient subgroup is
exactly the originally specified action.

The product topology is transported through the displayed coordinate
equivalence. The coordinate equivalence is a homeomorphism, and the
inclusion, projection and section are continuous. With topological group
structures, a continuous action, and a continuous cocycle, the group
operations are continuous by their coordinate formulas.

Source: Artin and Tate, *Class Field Theory* (2009), Chapter XIII section 1,
printed pp.127–128 (PDF pp.136–137), registered as
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The module implements their extension from a factor set in the normalized
case. The explicit topology is a derived construction proved using the
coordinate formulas. Mathlib's `groupCohomology.IsMulCocycle₂` supplies the
cocycle convention. No assertion identifying a cocycle with an arithmetic
fundamental class, or constructing a relative Weil group, is made here.
