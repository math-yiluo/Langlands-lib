# The point map of the affine ground field comparison

Under the fixed-radius hypothesis `hfixed`, this module builds the comparison of
the glued point spaces, from the actual ground field extension of the affine
analytification of `P` to the affine analytification of
`Q = baseChangePresentation K L P`.

`rawPoint i n` is the continuous map from the extended original chart spectrum
at `i` to the analytification of `Q`, through the spectrum map of `rawPull i n`
and the raw chart `n`. Passing to a larger raw chart does not change it
(`rawPoint_le`, `rawPoint_independent`). `chartPoint i` is its value at the
chosen level `level i`, whose radius bounds that of `i`. It respects the
extended source restrictions (`chartPoint_pull`) and so descends to the
common-subchart quotient as `pointFun`, with the chart formula
`pointFun_chart` and continuity `continuous_pointFun`.

`pointFun_projection` says that `baseChangeMap` composed with `pointFun` is the
projection of the extended space to the original analytification. It is
computed on original algebra elements. `range_chartPoint` identifies the image
of each extended chart with the `baseChangeMap`-preimage of the corresponding
original chart. It uses the represented radius restriction and the equality of
coordinate seminorm evaluations (`pointSeminorm_X`, `coordinateNorm_baseChange`).
Each `chartPoint i` is an embedding (`isEmbedding_chartPoint`): the spectrum
map of a representing bounded map is injective, and it is continuous from a
compact space to a Hausdorff space. These images form a quasinet covering the
target. So `pointFun` is bijective, by the embeddings, the projection formula
and the cover, and its inverse is continuous on each member of the quasinet.
Therefore `isHomeomorph_pointFun` holds; it sets `maxHeartbeats 1000000`.
