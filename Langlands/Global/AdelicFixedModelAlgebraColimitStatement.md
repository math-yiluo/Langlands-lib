# Actual adelic algebra colimits over a fixed initial integer base

This derived target continues `AdelicFixedModelSystem` and
`AdelicFixedModelCocone`. It supplies the coefficient universal property needed
for the fixed-model point comparison in Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), equation (3.5.1), printed p.6.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`.

For arbitrary fields `k` and `F` with a `k`-algebra structure and every finite
set `S` of actual discrete curve places, the canonical cocone
`curvePlaceAdeleOverCocone k F S` is a colimit in the category of commutative
algebras over the actual outside-`S` integer ring. Its diagram consists of the
actual adelic level rings at finite `T` containing `S`, with the original
integer inclusions and diagonals defining their scalar actions. Its maps are
literal inclusions and its vertex is the full actual curve-place adele ring.

For each number field `K` and every finite set `S` of finite places, the same
universal property holds for `numberFieldAdeleOverCocone K S`, in commutative
algebras over its actual `S`-integer ring. Every infinite completion remains in
every level and in the full adele ring. `AdelicFixedModelAlgebraColimitStatement`
is the conjunction of these two universally quantified propositions.

A colimit means that every compatible cocone of fixed-base algebra maps has a
unique algebra map from the actual full adele algebra factoring its components.
No candidate colimit or compatibility conclusion is an input to this target.
The intended derivation uses the published finite-level subring cover: enlarging
a finite exceptional set to its union with `S` gives a cover by levels in this
diagram. Compatible maps descend through that cover; compatibility with scalars
is checked on an initial-level scalar representative. This algebraic argument
requires no function-field presentation, perfectness or finite constant field,
and permits empty `S`. The common universe is arbitrary.

This target does not claim a colimit in topological algebras, point comparison
bijectivity, generic-fiber realization, or independence of the initial model.
Those remain distinct obligations in the paper's adelic-point construction.
