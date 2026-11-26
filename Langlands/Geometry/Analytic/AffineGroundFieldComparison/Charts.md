# Mixed-radius bounded pullbacks for the affine ground field comparison

Fix complete, ultrametric, nontrivially normed fields `K` and `L` with
`NormedAlgebra K L`, and a finite polynomial presentation `P` of a commutative
`K`-algebra `A`. The abbreviations `Q` for `baseChangePresentation K L P` and
`S` for the actual chart system of the ground field extension of the affine
atlas of `P` (from `GroundFieldExtensionChartSystem`) are fixed here, with `rK i` and
`rL n` for the polyradii of the original chart `i` and the raw `L`-chart `n`,
`E i` for the extended original chart algebra and `C i` for the chart algebra
of `Q` at the radius of `i`. Every other declaration of the module takes the
fixed-radius statement `AffineAnalytificationChartBaseChangeStatement` as the
explicit hypothesis `hfixed`; nothing else is assumed.

`eAt i` is the bounded `L`-algebra equivalence supplied by `hfixed` between the
extended `K`-chart at the original index `i` and the `L`-chart of `Q` at the
same radius. `eAt_algebraMap` records its value on `iota` of the image of `a`.
For a raw `L`-chart index `n` whose radius is at least that of `i`, `rawPull i n`
is the radius restriction of `Q` from radius `n` to the radius of `i`, followed
by the inverse of `eAt i`. It is computed on every `1 ⊗ a`
(`rawPull_algebraMap`) and on every coordinate (`rawPull_coordinate`).
Increasing the raw target radius is compatible by transitivity of radius
restrictions (`rawPull_comp`). Restricting the source chart along a containment
of extended charts is compatible (`rawPull_sub`); this is proved by bounded-map
extensionality on coordinates. Finally `rawPull i n` represents the
corresponding radius-bounded affinoid domain (`rawPull_represents`). This
follows from the representation property of radius restriction, transported
along the equivalence.

These are the chart-level inputs of the comparison; the point map and the
strong map are built in `AffineGroundFieldComparison.Points` and
`AffineGroundFieldComparison.Strong`.
