# Geometric character congruence over the maximal unramified field

For a nonarchimedean local field `F`, write `K = inertiaFixedField F`, which
is the actual maximal unramified field used by the building definitions.
Let `E/K` be a finite separable field extension. This module specializes
the general all-character congruence homomorphism to the normalized
coordinate valuation on `E` and the geometric valuation on
`SeparableClosure F`.

`henselianWeilUnitCongruenceHom F E hH r` maps the normalized depth-`r`
unit filtration in `Eˣ` to the depth-`r` character congruence subgroup of
the actual Weil restriction after geometric base change. It uses any
explicit Henselian proof `hH` for the normalized valuation ring of `K`;
the published `valuationSubring_isHenselian F` supplies such a proof.
The underlying point is `WeilGm.extendedUnitPoint` of the original unit,
as recorded by `henselianWeilUnitCongruenceHom_coe`.

The construction has no extra splitting or embedding-preservation
hypothesis. Finite separability and the separably closed target give
`WeilGm.separable_minpoly_splits`; `embeddingEvaluationStatement` then
supplies bijective tensor evaluation. The exact comparison
`henselianSeparableAddValuation_eq_geometric` proves preservation for
each embedding, recorded as `coordinateEmbedding_preserves_value`.
The general `weilGm_unitCongruenceHom` now applies.

`weilGm_geometricCharacter_bound F E hH hr t ht χ` is the positive-depth
form used by the coroot proof. A bound for the coordinate valuation of
`t - 1` gives the same bound for the geometric valuation of `χ(c) - 1`,
where `c` is the geometric extension of the rational Weil-restriction
point with unit coordinate `t`. It applies the previously proved
general positive-depth character bound with the same two inputs.

These are internal specializations of the named constructions and
proved comparisons. They do not assert existence of rank-one
coordinates or prove the building coroot statement by themselves.
