# Original point charts over a fixed lifted base

This internal adapter for the finite vector-bundle filtrations of supplied
relative radicals starts with actual natural module charts on
tests carrying a lift to a covering scheme. Equal lifts are compared through
the canonical module pullback-congruence isomorphism.

`natural_comp` retains the original point and the exact canonical module
comparison for any specified composite lift. Given a fixed lift of a base
map, `atLift` constructs natural point charts for the actual pulled-back group
and the actual pulled-back module on every test over that base. It uses the
original group pullback point equivalence and the prescribed module
pullback-composition section equivalence. `atLift_apply` gives the exact
original point-section formula.

The provenance is derived from the original lifted chart naturality and actual
group and module pullback coherence. No scalar preservation or module overlap
cocycle is assumed or proved here.
