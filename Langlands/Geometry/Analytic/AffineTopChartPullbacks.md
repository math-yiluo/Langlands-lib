# Full pullbacks from bounded greatest-chart pushouts

This internal construction uses the Library's actual bounded pullbacks of
complete strong morphisms and its reconstruction of strong morphisms from
compatible chart algebra maps. No external result is transcribed.

Let `K : Type u` be a complete ultrametric normed field. All presentations have
space universe `v` and atlas index universe `w`, independently of `u` and of
one another. Morphisms in `SaturatedAtlasPresentation` are the complete strong
morphisms, including every admissible bounded chart pullback.

`StrongHom.pullbackAtTop` retains the actual bounded pullback to a specified
greatest target chart, for each original source chart. Its source restriction
law follows from the strong map's existing naturality. `StrongHom.ext_atTop`
shows that equality of these bounded maps determines the entire strong
morphism. The proof extracts local chart data from the first map and observes
that both maps realize exactly those data. The existing uniqueness theorem in
`DirectedAtlasReconstruction` identifies both maps with the reconstruction.
Thus this argument retains algebraic information even for nonreduced algebras;
equality of spectrum point maps is not its equality criterion.

Consider strong morphisms `p : P ⟶ A`, `q : P ⟶ B`, `f : A ⟶ C`, and
`g : B ⟶ C`. Choose chart indices `tP`, `tA`, `tB`, and `tC`, with greatest
chart hypotheses on the last three. `TopChartPushout` means the following
bounded-algebra universal property. For every presented affinoid algebra `E`
and bounded maps from the algebras of `tA` and `tB` to `E` agreeing after
composition with the greatest-chart maps of `f` and `g`, there is a unique
bounded map from the algebra of `tP` to `E` whose composites with the maps of
`p` and `q` are the two given maps. This definition does not itself assert
commutativity of the strong square or that `tP` is greatest. The categorical
consequences assume both explicitly.

`pullbackAtTop_comp` computes categorical composition as the literal bounded
composite through the specified greatest intermediate chart. For every
commuting cone `a : T ⟶ A`, `b : T ⟶ B`, applying this formula to its equality
gives compatible bounded maps on each chart of `T`.

`TopChartPushout.existsUnique_lift` additionally assumes that `tP` is greatest.
Apply bounded-algebra universality separately with the algebra of each chart
of `T` as test algebra. Uniqueness shows that the resulting bounded maps
commute with every source restriction: restriction followed by the map on the
larger chart has the same two projected composites as the chosen map on the
smaller chart. These maps therefore form `LocalChartMapData` with constant
target index `tP`. The greatest chart supplies directedness, and
`LocalChartMapData.toStrongHom` constructs the actual ambient continuous map
and all admissible bounded pullbacks. Its selected pullback formula, bounded
factorization equations, and `ext_atTop` give both exact projection equations.
The same bounded uniqueness on every source chart proves uniqueness among
all complete strong lifts. There is no greatest-chart assumption on `T`.

When `p ≫ f = q ≫ g`, `TopChartPushout.hom_ext` obtains joint uniqueness of
the projections from that unique lifting result. `TopChartPushout.isLimit`
then supplies a lift and both factorization equations for every categorical
pullback cone and uses joint uniqueness for its uniqueness field.
`TopChartPushout.isPullback` packages the resulting full categorical limit.

This is a conditional internal affine construction. It has no Hausdorff or
compactness hypotheses, and it preserves all three universes. It does not
construct a global analytic pullback, prove any etale assertion, or assert that
ordinary points of an analytic pullback are determined by a pair of projected
points. Specializing the bounded-algebra criterion to a concrete small
affinoid pushout and constructing and gluing the general etale pullback remain
separate obligations.
