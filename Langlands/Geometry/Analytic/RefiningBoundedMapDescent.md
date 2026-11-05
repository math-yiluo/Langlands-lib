# Bounded algebra-map descent along a refining original subatlas

This module constructs extension of a compatible family of actual bounded algebra maps from a refining selection of original affinoid charts to every original chart. It is an internal construction from the existing compact chart-refinement, full-domain bounded-map gluing and algebra-separation results. It asserts no new correspondence with an original-literature statement.

The base field `K : Type u` is a complete normed field with ultrametric distance. The atlas lives on a topological space `X : Type v`, with chart indices in an independent universe `w`. The input algebra `R : Type z` is any normed commutative ring with a normed `K`-algebra structure; it need not be complete or affinoid. No nontrivial-valuation, reducedness, nonemptiness or source-saturation hypothesis is added.

## Input and overlap construction

`SelectedBoundedMapFamily a P R` supplies a bounded `K`-algebra map from `R` to the unchanged algebra of each original chart selected by `P`. Its only equations are compatibility with original restriction maps whenever one selected chart is contained in another. Here `P : a.RefiningSelection` includes downward closure and the original local finite-neighborhood refinement condition. No map on an unselected chart and no gluing result are input data.

`SelectedBoundedMapFamily.overlap` proves compatibility on every actual full domain `W` mapping to two selected charts inside the same parent chart. The compact image of `W` has a finite common-chart refinement of those two charts. Each common chart is selected by downward closure. The structural triangles for the full-domain maps and uniqueness of bounded factorization identify the restricted maps with original chart restrictions. Input naturality identifies both resulting maps on every common chart. Full-domain algebra separation then proves equality on the entire stored algebra of `W`, for each input element of `R`. The argument uses all algebra data, including data not detected by spectrum points.

## Actual bounded gluing and recovery

For any `FiniteSelectedChartCover` of a parent chart, `finiteCover_compatible` applies the preceding overlap result to its actual full-domain cover. `glueOnCover` uses the existing `Domain.FiniteCover.glueBoundedAlgHom` construction to obtain a bounded map into the original parent algebra with its stored norm. That imported construction glues algebra elements and proves boundedness using the finite-cover restriction estimate; this module does not replace the parent algebra or its norm. `restriction_comp_glueOnCover` recovers each supplied finite-cover member.

`restriction_comp_glueOnCover_of_selected` proves recovery on every selected chart contained in that parent, including charts absent from the chosen finite cover. Intersect its actual restriction domain with every cover member. These intersections form a finite cover of the selected restriction domain. The two structural triangles, finite-cover recovery and the overlap theorem give equality on each intersection. Full-domain algebra separation gives the asserted equality of complete bounded maps on the selected chart.

## Extension, naturality and uniqueness

`extend` uses compactness to choose a finite selected chart cover of each parent and applies `glueOnCover`. `restriction_comp_extend` recovers the prescribed map on every contained selected chart. `extend_selected` specializes this to the identity restriction on a selected parent.

`extend_naturality` proves all original restriction equations between arbitrary parent charts. Restrict both candidate maps to any selected chart contained in the smaller parent. The original restriction composition law and the recovery theorem give equal maps there. `boundedAlgHom_ext_of_refiningSelection` concludes equality on the complete parent algebra.

`extend_unique` applies the same separation result to any family on all original charts satisfying all restriction equations and agreeing with the input family on selected charts. It proves equality with `extend` on every chart. Consequently, the extension is independent of the finite covers chosen in its construction, in the precise sense that every extension with these properties equals it.

This is bounded-algebra descent on original atlas charts. The construction of strong-map extension, the fully faithful affinoid embedding into the source quotient, full analytic identification, and the etale/equivariant sites remain separate obligations.
