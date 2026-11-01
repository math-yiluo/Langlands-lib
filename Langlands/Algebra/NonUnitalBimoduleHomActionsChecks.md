# Residual original Hom action interface checks

Author: Worker 702. This internal companion imports
`NonUnitalBimoduleHomActions`; that module's paired Markdown supplies the
source citations, intrinsic proof explanations and mathematical limits.
No new source assertion is made here.

The private interface abbreviations spell out complete dependent function
types for `sourceAction`, `targetAction`, `actionsCommute`, `hom`,
`rightSourceAction`, `regularSourceAction`, `fromRegular`, `toRegular`,
the three complete scalar-endomorphism formulas and
`regularSourceAction_compat`. Each `example` assigns the corresponding
unapplied declaration to that type. This tests the full declaration,
including binder order, specified structures and the maximum Hom carrier
universe; applying some arguments cannot mask a mismatched interface.
The examples use arbitrary independent ring and carrier universes, then
unequal 0/1 assignments and their reversals. The universe linter is
disabled for these private interface abbreviations because their sort
intentionally aggregates all universes by a maximum; no type equality
or kernel check is disabled.

The `Competing` section places two ring instances on each scalar carrier,
two group instances on each vector carrier, alternative original actions
and alternative actions on the exact Hom carrier in scope. Explicit
applications and explicit bundle projections verify the chosen Hom
carrier, inherited group, source action and target action definitionally.
`RegularCompeting` similarly checks both linear adapters with competing
ring, target-group, target-action and Hom-action instances present.
The overlapping-instance linter is locally disabled for these intentional
examples only.

The subsingleton examples apply the core lemmas to the actual bundled Hom
with either the source or the target subsingleton, for arbitrary original
actions. The integer-zero example chooses zero original actions on the
nonzero group `ℤ` for arbitrary `S` and arbitrary unital residual rings
`R,T`. Its identity original intertwiner is nonzero: equality with the
zero map would imply `(1 : ℤ) = 0` by evaluation. The two generic
zero-action lemmas then show that every left and every right scalar
endomorphism of this entire nonzero Hom is zero. This checks the allowed
degenerate case even when both residual rings have units. The last
example uses the integer regular action and the identity regular-source
map to check the formula `fromRegular (a • φ) b = b*a`.

These checks establish interfaces and the stated examples. They do not
assert Hom nondegeneracy, tensor-Hom isomorphisms, adjunction, exactness,
coefficient-scalar or unitization compatibility, or any of the source's
forgetful or induction functors.
