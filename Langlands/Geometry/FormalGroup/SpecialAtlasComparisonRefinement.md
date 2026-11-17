# Source squares for refinement through supplied scalars and reduction

This is internal coherence infrastructure for actual special formal atlases.
It transports the mixed refinement and coefficient extension square from
`AtlasOrderComparisonBaseChangeRefinement` through equality of scalar algebra
structures, then specializes it to quotient reduction. It makes no additional
original-literature assertion.

For two specified comparisons `c,d : Comparison X Y`,
`ComparisonSourceSquare c d` is the proposition that there are equalities of
their respective left and right finer covers, together with the equality

```text
sL.trans d.coordinateIso = c.coordinateIso.trans sR,
```

where `sL` and `sR` are exactly the existing `orderSourceIso` maps from the
refinements of `c` to those of `d`. The proposition retains these actual
source-change maps. It permits different selected original charts and does not
assert equality of the two comparisons. The equality concerns complete
order-linear formal isomorphisms, rather than only their effects on points.

`ComparisonSourceSquare.symm` reverses this square. The reverse source maps are
definitionally the inverse maps of the original source isomorphisms. Taking
forward maps in the supplied equation, composing with both actual inverses,
and using associativity and the two inverse equations proves the reverse
equation. Extensionality of formal isomorphisms then recovers the whole square.

`reAlgebraComparisonRefinement` transports a further refinement alongside the
existing `reAlgebraComparison`. The theorem `reAlgebraComparison_refine`
identifies scalar retyping of the specified refined comparison with refinement
of the retyped comparison by that transported cover.
`comparisonSourceSquare_reAlgebra` transports the whole source-square
proposition, including its two cover equalities and actual formal-map equation.
All three constructions eliminate the equality of scalar algebra structures;
they introduce no new chart choices.

Given `g : Comparison X Y`, a further principal refinement `q` of its left
refined atlas, and an arbitrary supplied scalar map `f : R →ₐ[𝒪[K]] S`,
`baseChangeAlongComparisonRefinement g q f` is the image refinement on the left
atlas of the supplied-target extended comparison. It first uses the constructed
`g.baseChangeRefinement` and then retypes its scalars using
`coefficientAlgebraAlong_eq f`. With

```text
L = baseChangeAlongComparison (g.refine q) f,
M = (baseChangeAlongComparison g f).refine
      (baseChangeAlongComparisonRefinement g q f),
```

`baseChangeAlongComparison_refine_source_square` proves
`ComparisonSourceSquare L M`. Its proof takes the actual mixed formal-map
equation from `AtlasOrderComparisonBaseChangeRefinement`, transports it to the
supplied target scalar structure, and uses `reAlgebraComparison_refine` to
identify the retained comparison. The coefficient test is bound before
installing its induced algebra structure, so it keeps the original supplied
scalar map.

For an object `A : Nilp R r`,
`reductionComparisonRefinement g q` specializes this image refinement to the
actual quotient map `Nilp.quotientO 𝒪[K] A`.
`reductionComparison_refine_source_square` gives the same source-square
equation between `reductionComparison (g.refine q)` and the specified
refinement of `reductionComparison g`. No equality of independently selected
original sources is required, even when the quotient merges cover generators.

The parameters retain a nonarchimedean local field `K`, its finite-dimensional
central division algebra `D`, the embedded field `L`, and commutative
coefficient rings with their supplied `𝒪[K]`-algebra structures. Both rings in
the supplied-map construction have universe `v`; the reduction specialization
uses `A : Nilp.{v,u} R r`. Covers need not be finite, and coefficient maps need
not be injective or flat. The unit proves reduction/refinement coherence for
the specified actual comparisons. Framing preservation, original framed
composition, finite-chain collapse, varying-base framed functoriality, group
actions and representability remain separate constructions.
