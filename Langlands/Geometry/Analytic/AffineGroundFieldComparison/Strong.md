# The strong affine ground field comparison, from the fixed-radius statement

Under the fixed-radius hypothesis `hfixed`, this module upgrades the point map
of `AffineGroundFieldComparison.Points` to a compatible strong
quasi-isomorphism. Its source `src` is the actual scalar-extended affine atlas
of `P`; its target `tgt` is the affine atlas of
`Q = baseChangePresentation K L P`.

`admissible i j` says that the point map carries the extended source chart `i`
into the target chart `j`; `exists_admissible` gives one such `j` for each `i`.
It uses the raw radius bound and the chosen representative of the range of a
raw chart. For an arbitrary admissible pair, `large i j` is a raw `L`-chart
dominating both, and `largePull i j` the corresponding mixed-radius pullback.
It has image in the domain of the restriction from `large i j` to `j`
(`hasImageIn_largeRes`). So by the universal property of affinoid domains it
factors uniquely through that restriction (`existsUnique_fact`); the factor is
`fact i j h`. It satisfies the chart equation (`fact_chart_comm`), computes on
`1 ⊗ a` (`fact_algebraMap`) and on coordinates (`fact_coordinate`), and
represents the full image locus (`fact_represents`). The last uses
cancellation for the injective spectrum map of the target restriction.

For the restriction square `fact_restriction_comm`, both composites are
precomposed with the restriction from a still larger raw chart `n`. By
transitivity of raw restrictions (`rawRestriction_trans`) and `fact_comp_at`,
each factor precomposed with such a restriction is the mixed-radius pullback
`rawPull` at `n`; the source restriction then carries one pullback to the other
(`rawPull_sub`). The restriction from `n` to the larger target chart represents
an affinoid domain, so maps out of its target are determined by their
precomposition with it, and the square commutes. No numeric radius inequality
is attributed to a containing target chart: the target chart of an admissible
pair may have a smaller radius than the source chart.
`comparison` is the resulting `StrongHom`. `compatibleComparison` adds
compatibility, which follows from the directed target atlas, and
`comparison_isQuasiIso` combines the homeomorphism with `fact_represents`.

`reduceStrongComparison` derives
`AffineAnalytificationGroundFieldComparisonStatement` from the fixed-radius
statement `AffineAnalytificationChartBaseChangeStatement`: the witness is `compatibleComparison`, with
`comparison_isQuasiIso`, `pointFun_projection` and `fact_algebraMap`.
