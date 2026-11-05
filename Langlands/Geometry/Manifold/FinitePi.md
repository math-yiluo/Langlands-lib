# Finite products with normed-vector-space chart models

Author: Worker 94. This internal construction assembles Mathlib's finite-product
charts and componentwise differentiability results. It supplies a finite-product
manifold helper for the subsequent actual archimedean group construction.

Let `ι` be any finite type with a specified `Fintype` instance. For each `i`, let
`E i` be a normed vector space over a common nontrivially normed field `𝕜`, and
let `M i` be a topological space with specified charts modelled on `E i`.
The index, coefficient field, chart models and spaces may have independent
universes. No dimension, completeness or nonempty-index hypothesis is imposed.

`finitePiChartedSpace E M` uses Mathlib's exact `piChartedSpace E M`, with its
model explicitly presented as the normed Pi vector space `∀ i, E i`. The
product retains the ordinary product topology. The atlas consists of finite
products of the component atlas charts, and the preferred chart at a point is
the product of the component preferred charts at its coordinates. The named
constructor is passed explicitly in subsequent statements rather than
registered globally over the untagged model.

`finitePiIsManifold` assumes that every specified component charted space is
an `IsManifold` of the same order `n`, where `n : ℕ∞ω` may also be the analytic
order. It proves that these product charts are an `IsManifold` over
`𝓘(𝕜, ∀ i, E i)`. The proof checks chart transitions. Each component is the
corresponding component transition after the continuous linear projection,
on the product transition domain. Component manifold compatibility gives
smoothness of each transition, composition gives smoothness after projection,
and `contDiffOn_pi` assembles the components.

`contMDiffAt_finitePi_iff` identifies smoothness at a point of a family into the
product with smoothness at that point of each component. The source is any
charted space, with an arbitrary model with corners over the same field.
Neither the source nor the component spaces need a manifold hypothesis for
this criterion: it uses their specified preferred charts directly.
The proof unfolds `contMDiffAt_iff`; continuity and differentiability within
the range of the source model both split componentwise.
`contMDiff_finitePi_iff` quantifies this equivalence over all source points,
and interchanges the two universal quantifiers.

The construction uses vector-space models on the factors and their product.
It does not construct a product for arbitrary factor models with boundary or
corners. Its provenance is internal use of the pinned Mathlib charted-space,
smooth-groupoid and differentiability definitions; no original-literature
result is transcribed.
