# Coordinate map of the scalar-extension Weil unit

For a commutative ring `A`, a finite projective commutative `A`-algebra `B`,
and a finite-type commutative `A`-algebra `C`,
`Langlands.Algebra.WeilRestrictionFiniteType.tensorUnit` is the canonical
algebra map

`WeilRestrictionFiniteType A B (B ⊗[A] C) →ₐ[A] C`.

It classifies the identity of `B ⊗[A] C` under the existing finite-type
Weil-restriction representing bijection. Consequently its scalar extension
composed with the universal point is the identity. This constructs a
section and proves scalar-extended surjectivity.

If `B` is faithfully flat over `A`, `tensorUnit_surjective` descends this
surjectivity using Mathlib's faithful-flat tensor criterion for linear
maps. `tensorUnit_natural` records naturality in `C`, by the representing
bijection's naturality and its functoriality in the input algebra.

This is internal derived infrastructure for the actual scheme and group
unit into a Weil restriction after scalar extension. The proof uses only
the published finite-type representing property and Mathlib's
faithful-flat reflection of surjectivity. It does not assume a retraction
before scalar extension or a closed immersion. For every finite field
extension the faithful-flat hypothesis holds. No separability, topology,
character kernel or compactness conclusion is asserted here.
