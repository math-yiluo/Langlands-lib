# Pullback and composition of locally reindexed coefficients

This internal derived module extends structure-sheaf coefficient gluing with
pullback, composition and uniqueness. It uses only the previously constructed
local reindexing data and the sheaf naturality and uniqueness laws.

`intersection_covers` proves that pairwise intersections of two covers still
cover the scheme. `Datum.pullback` pulls a datum to any scheme morphism by
inverse-image opens and the same permutations. A point of a nonempty pulled-back
intersection maps to a point of the original intersection, so compatibility
follows. `restrict_appTop` is naturality of the structure-sheaf morphism at a
global section. `equiv_pullback` checks the pullback formula on all inverse-image
opens using that naturality and the local reindexing formula.

`Datum.comp` takes the intersection cover and composite coordinate equivalences.
`comp_restrict` and `equiv_comp` prove that its glued algebra equivalence is the
composition of the two glued algebra equivalences, by checking both on each
intersection.

`equiv_eq_of_agree` proves equality of glued algebra maps whenever their local
permutations agree on every nonempty intersection of their covers. Empty
intersections have unique sections. `equiv_eq_of_unitTransform` derives that
permutation equality when both data locally describe the same transformation
of unit families on all relative tests, using the separating-test lemma.

The universe is arbitrary and common to schemes and index types. No finiteness,
affineness or nonemptiness of the base or indices is assumed here. This module
supplies general coherence laws; it does not yet construct a coefficient descent
coaction from a group-scheme atlas.
