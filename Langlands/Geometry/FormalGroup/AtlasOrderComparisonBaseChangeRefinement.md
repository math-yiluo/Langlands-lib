# Refinement and coefficient extension of a specified comparison

This module constructs the further refinement needed to compare two orders of
operations on an actual order-linear atlas comparison, and proves their
compatibility through the specified source-choice isomorphisms. It is derived
internal content from `AtlasOrderComparisonBaseChange`,
`AtlasOrderComparisonEquivalence`, and the refinement and source-choice
constructions imported by `AtlasOrderComparisonInverse`. It makes no new
original-literature claim.

Let `c : Comparison E E'`, let `q` refine `c.left.atlas`, and let `S` be any
commutative `R`-algebra. There are two comparisons of the extended actions:

- `L = (c.refine q).baseChange S`;
- `M = (c.baseChange S).refine (c.baseChangeRefinement q S)`.

`baseChangeRefinement` has the image cover `q.atlas.baseOpens S`. Its source map
and unit-containment proof are the actual ones from `q.baseChange S`, viewed as a
refinement of `(c.left.baseChange S).atlas`. This constructs `M` without assuming
that extension preserves the previously selected original source chart.

The left and right refinements of `L` and `M` have the same respective covers.
Let `sL` and `sR` be their existing `orderSourceIso` maps, directed from `L` to
`M`. The theorem `baseChange_refine_source_square` proves the equality of
whole order-linear formal isomorphisms

```text
sL.trans M.coordinateIso = L.coordinateIso.trans sR.
```

In particular, the equality retains the actual coordinate isomorphisms of both
construction orders and both source corrections. It does not identify the
different selected source charts by assumption.

The supporting theorem `coordinate_transport_independent` concerns any two
invertible charts `a,b` of `c.right` over a fixed test algebra `A`, and any
invertible original charts `x` of `X` and `y` of `Y`. Transporting
`c.coordinateIso` from `x` to `y` through `a` gives the same complete coordinate
map as transporting it through `b`. The proof takes the complete coordinate map
of the comparison's transition equation, rewrites both refined transitions as
original transitions, and applies the two original atlas cocycle equations and
associativity.

For the mixed square, extensionality reduces equality of the isomorphisms to
their whole coordinate maps on each test chart. The construction formulas for
refinement, coefficient extension and source correction reduce this equation
to composites of original transitions with the original comparison map.
The two cocycles remove the intermediate original charts.
`baseSource_sourceChart` identifies the selected left finer chart with the
transport of the selected right finer chart; equality of transition coordinate
maps handles the dependent unit witnesses. The supporting transport theorem
then proves the remaining equation. Equality of point families is not used to
deduce equality of formal maps.

The assumptions are commutative `O` and `R` with an `O`-algebra structure, a ring
`D` with an `O`-algebra structure, full `D`-actions, and finite coordinate types
which may differ. The covers may be infinite and the original covers may
differ. There is no injectivity or flatness hypothesis on the coefficient map,
so image generators may merge. No fraction field or rationalization is needed.

Compatibility of original framed comparisons with quotient reduction,
composition of those comparisons, finite-chain collapse, varying-base framed
functoriality, group actions and representability remain separate obligations.
