# Comparing actual solutions over nested base restrictions

This is an internal supporting construction for gluing affine-local descent
solutions. It is derived from the existing restriction, pullback-comparison and
surjective étale homomorphism-descent interfaces. It makes no new assertion of
object effectivity and cites no independent source theorem.

Fix schemes in universe `u`, a map `p : S → B`, an actual group scheme `G/S`,
and a Čech descent datum `D`. Consider a first commuting square with
`t : V → C`, `q : V → S`, `b : C → B`, and `q ≫ p = t ≫ b`.
Consider a second square `r : W → E`, `v : W → V`, `c : E → C`, with
`v ≫ t = r ≫ c`. Choose direct composite representatives `q' : W → S` and
`b' : E → B`, with `v ≫ q = q'`, `c ≫ b = b'`, and
`q' ≫ p = r ≫ b'`.

`Datum.reindex_comp_compatible_of_eq` identifies the iterated restricted datum
with the directly restricted datum through the actual group pullback comparison.
Its proof substitutes the chosen composite representatives and applies existing
restriction associativity. `collapseReindexSolutionOfEq` transports a supplied
solution along that compatible isomorphism. `localRestriction` applies this to
the restriction of a supplied solution `s` of the first datum. Its descended
group is definitionally the base change of `s.obj` along `c`, as recorded by
`localRestriction_obj`. `localRestriction_proj` proves that its actual quotient
map, followed by the projection to `s.obj`, equals the canonical map from the
directly restricted covering group to the first covering group followed by
`s.schemeProj`. This formula follows by expanding restriction and comparing
projections through the pullback isomorphisms. The shared inverse square
comparison lemma `squareComparison_inv_fst_fst` in
`Langlands.GroupScheme.Descent.SquareComparisonProjection` preserves the original group
projection as well.

For a surjective étale cover, the generic lemmas
`Solution.descendHomOfEtale_schemeProj` and
`Solution.descendIsoOfEtale_schemeProj` show that descended compatible maps
commute with the supplied quotient maps. Their proofs use exact pullback
recovery and naturality of the pullback projection.

Now assume only that the smaller map `r` is surjective and étale, and supply
both the larger solution `s` and a chosen solution `a` of the directly
restricted smaller datum. `Datum.localSolutionComparison` descends the identity
of that common datum to an isomorphism
`a.obj ≅ (GroupScheme.baseChange c).obj s.obj`.
`localSolutionMap` is its underlying scheme map followed by the projection to
`s.obj`. No affineness, quasi-compactness, or étaleness of the other square maps
is assumed.

`localSolutionMap_proj` gives the exact quotient equation described above.
`localSolutionMap_square` transports the canonical pullback square along the
comparison isomorphism, proving that the smaller quotient is the base change of
the larger quotient along `c`. `localSolutionMap_unique` cancels the smaller
surjective étale quotient projection, so the quotient equation uniquely
characterizes the transition map. These constructions compare supplied local
solutions; they do not by themselves glue them or prove the main quasi-split
inner-form existence statement.
