# Rank-one laws on every scheme test and their descent

`LocalSplitCell.RankOneLaws i nu xp xm` records four identities for
actual opposite additive-group maps into a group scheme over a commutative
ring. Every identity is asserted on every scheme test over that ring:

- If `N` is the constant family of `xm(-1) xp(1) xm(-1)`, then
  `N xp(x) N⁻¹ = xm(-x)` and `N xm(x) N⁻¹ = xp(-x)`.
- The square is `N N = i(nu(-1))`.
- Whenever a supplied unit `d` has value `1 + x*y`, the relation is
  `xp(x) xm(y) = xm(d⁻¹*y) i(nu(d)) xp(d⁻¹*x)`.

The fixed exponent vector `nu` defines a point of the standard split
torus by taking coordinate powers of the supplied global unit. No
locality, reductivity, reducedness, or characteristic hypothesis is
imposed on this interface. It records laws, without asserting that an
arbitrary supplied pair satisfies them.

`comp_cocharPoint` proves naturality under restriction of the test by
applying the split-torus coordinate equivalence and compatibility of
unit powers with a monoid homomorphism. The two coefficient-extension
lemmas identify fixed-exponent cocharacter points and constant Weyl
products under the actual base-change point equivalence. They use the
standard split-torus comparison and the coordinate-preserving comparison
for the additive group.

`RankOneLaws.of_baseChange` proves descent from a commutative coefficient
algebra `A` when pullback along `Spec A → Spec R` is faithful. For each
original test `Z`, the counit of the map-pullback adjunction is an
epimorphism from the mapped pullback test to `Z`. The proof maps the
four assumed coefficient-ring laws through the group-valued point
equivalence, identifies their coordinates by the preceding lemmas, and
cancels that epimorphism. The global functions and the denominator unit
are restricted by the counit's map on global sections. Ring-homomorphism
compatibility preserves `d = 1 + x*y` and inversion of the unit.

This is an internal derived interface and descent argument, using actual
scheme morphisms and their point-coordinate equivalences. It neither
assumes field-point detection nor discards nilpotents. Constructing the
laws for the supplied root maps of a reductive group, specializing them
to the local rank-one statements, and proving the full local Isomorphism
Theorem remain separate obligations.
