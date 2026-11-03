# Positive relative root subgroups lie in dynamic unipotent subgroups

This internal construction contracts the existing actual root subgroup functor
along a cocharacter with positive lattice pairing. It uses its defining orbit
extension and does not need a smooth root-group realization or a structural
root-system theorem.

`AffineLine.powerMap B m` is the morphism of the actual affine line defined by
the coordinate function `t^m`. On the unit locus it agrees with the `m`-th power
map of `Gm`. For `m > 0` it fixes the zero section, so pulling an extension back
along it preserves the extension's value at zero.

Given a character `a` and a cocharacter `ν` with `ν a` equal to the `m`-th power
map for a positive natural number `m`, pull an `a`-orbit extension back along
`t ↦ t^m`. Its restriction to the unit locus is the conjugation orbit of `ν`,
and its zero value is still the identity. This proves the inclusion in
`Dynamic.unipotent (ν ≫ i)` on every test scheme, over an arbitrary base.

Over a field, the existing lattice pairing identifies `ν a` with the integer
power map. A positive pairing is the cast of its positive natural-number part,
so the preceding argument applies. If `a` is simple and positive, every
cocharacter standard for the empty index has positive pairing with it. The
root subgroup therefore lies in the intersection defining the minimal standard
unipotent subgroup, and hence in the minimal standard parabolic.

All statements are derived from the published lattice pairing, root subgroup,
and dynamic subgroup definitions. No nontriviality of rational root-group points,
opposite-cell intersection theorem, or geometric Tits axiom is asserted here.
