# Canonical solutions on the covering scheme

This internal construction uses the actual transition isomorphisms of
`Descent.Reindex` and the restriction constructor of `Descent.Refinement`.
It constructs a solution after restricting the base to the original
covering scheme. All schemes lie in one arbitrary universe; no geometric
properties of the maps are assumed.

Let `D : Datum p G` for `p : S → B`. If `r, a : W → S` satisfy
`a ≫ p = r ≫ p`, then `Datum.transitionSolution r a w` is a solution of
`D.reindex r a p w`. This reindexed datum is on `r` over `S` with covering
group `a*G`. Its descended group is `G` itself, and its comparison is the
inverse of the original transition `a*G → r*G`.

`transition_canonicalCompatible` proves that the forward transition
respects the reindexed datum and the canonical datum on `r*G`.
For its two overlap coordinates, naturality turns the pulled-back
transition into the transition of the composite endpoints.
The two sides of compatibility are then equal by `Datum.transition_comp`.
The solution uses the inverse compatibility equation.

The helper `map_transition` is the published transition pullback formula
with its source comparison moved to the other side. The helper
`canonicalOverlap_eq_squareComparison` identifies the canonical overlap
with the commuting-square comparison by comparing their projections to
the original group scheme.

This is a solution over the original covering scheme `S`. It does not
construct a descent solution over `B` or prove the quasi-split inner-form
existence theorem.
