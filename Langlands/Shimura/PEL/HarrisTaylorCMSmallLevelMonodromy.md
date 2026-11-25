# Finite-order monodromy at a small Harris level

Both declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.
`primeTateMonodromyAt` is the existing rational prime Tate monodromy for
the rational prime corresponding to a finite place `v` of `ℚ`. Its
prime-power unit witnesses come from the witnesses for the full rational
Tate module.

`primeTateMonodromyAt_eq_one_of_smallLevel` concerns a positive polarized
action and a monodromy-invariant orbit of actual Weil-compatible adelic
frames at a Harris level `U`. If the full rational Tate operator of an
element of the geometric fundamental group has finite order, its action
on the rational prime Tate module at `v` is the identity whenever
`LevelSmallAt U v` holds.

The proof takes a representative of the invariant orbit. The action of
the fundamental group element on this frame equals right translation by
an element of `U`, via the scalar extension equivalence. Since the two
actions commute, a power of the fundamental group element acts on the
frame by the matching power of the level element. Finite order of the
full Tate operator fixes the frame for some positive power. Freeness of
right translation then makes the matching power of the level element
the identity. Projecting to `v` and using `LevelSmallAt` makes the
original level element's projection the identity.

In inverse-frame coordinates, monodromy acts by right multiplication by
the level element. After evaluation at `v` every coordinate is fixed.
The Library's local frame comparison gives equality after prime
extraction. Equivariance and surjectivity of prime extraction give the
identity on the actual rational prime Tate module.

## Provenance

Derived from the Library's invariant right orbits, the free action on
Weil-compatible frames, the published smallness condition, and local
frame comparison and equivariant prime extraction. The geometric argument
that supplies finite order for inertia is a separate prerequisite.
