# Further refinement of specified framed comparisons

This is an internal consequence of the actual quotient-reduction source square,
reduced framing refinement and framing transport through source changes. It makes
no additional assertion from the original literature.

Let `X` and `Y` be the supplied framed special formal-module atlases over the same
object `A` of `Nilp`, and let `g` be a specified comparison of their original
targets. A `FramingSquare e g` is the rational framing equation for the actual
quotient-reduced comparison `SpecialAtlas.reductionComparison g`, where `e`
identifies the stored residue maps. For any further principal refinement `q` of
`g.left.atlas`, `FramingSquare.refine` proves
`FramingSquare e (g.refine q)`.

The proof first refines the existing reduced framing square using the constructed
`SpecialAtlas.reductionComparisonRefinement g q`. Its comparison is

```text
(reductionComparison g).refine (reductionComparisonRefinement g q).
```

The source square from `SpecialAtlasComparisonRefinement` relates that comparison
to `reductionComparison (g.refine q)`. The proof reverses this square using the
actual inverse source-change formal maps and applies
`ReducedFramingSquare.of_source_square`. The result is therefore the framing
certificate for the reduction of the specified original refined comparison.
It does not require the independently selected original source charts to agree.
The imported source-square and framing-transport results compare complete
order-linear formal maps and their rationalizations in the actual tensor Hom.

`Comparison.refine f q` packages exactly `f.targetComparison.refine q`, the
unchanged `f.residue_eq`, and this proved framing certificate. The two projection
lemmas `refine_targetComparison` and `refine_residue_eq` are definitional
equalities; the construction does not choose another comparison representative.

The parameters retain the supplied nonarchimedean local field, finite-dimensional
central division algebra and embedded field, coefficient ring and residue field,
height-certified fixed frame and one `Nilp.{v,u}` object. Covers may be infinite,
original covers may differ, and the quotient map may merge generators. No
representing or universal object is assumed. Composition of original framed
comparisons, finite-chain collapse, varying-base functoriality, group actions and
representability remain further obligations.
