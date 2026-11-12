# Actual fibre points from the algebraic-space Lang–Weil estimate

This derived internal construction gives finite-field points needed in the
integral-surjectivity step of Conrad's Theorem 5.9. It assumes the exact
published `SpaceUniformLangWeilStatement`; it does not prove that estimate.

`nonempty_fibre_of_bound` applies the published numerical theorem
`Langlands.AlgebraicGeometry.langWeil_count_pos` to the cardinality of the
actual fibre of `RingPoints.map f`. When the positive field cardinality is
larger than the square of a nonnegative error constant, this cardinality is
positive, including in relative dimension zero. The positive-cardinality
criterion supplies a point of that fibre. `surjective_of_bound` applies the
same argument for every target point. These two lemmas retain an arbitrary
original coefficient base.

`pointLifts` applies the exact algebraic-space estimate to a supplied actual
étale morphism chart with surjective source and smooth scheme map of relative
dimension `d`. The base is quasi-separated and of finite type over the lifted
integers, and the morphism is separated, quasi-compact, surjective and has
geometrically connected fibres, exactly as required by the estimate. A single
positive real constant works for every finite field, every compatible
coefficient algebra and every target point, with an actual source point and
the exact point-map equation. No comparison with the residue field of the
image point is needed because the space estimate already quantifies over all
finite fields and their points.

The geometric premises, fixed relative dimension and uniform estimate are
explicit inputs. This module supplies neither a dimension decomposition nor
arithmetic models, Henselian integral lifts or the exact adelic endpoint.
