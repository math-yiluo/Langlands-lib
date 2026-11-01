# Induced actions on arbitrary supplied affinoid atlases

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

This module constructs coset-copy induction of a categorical subgroup action
on any supplied affinoid atlas presentation, including atlases with overlapping
or properly nested charts. For an open subgroup and a jointly continuous source
point action, it constructs the atlas and bounded action on the actual balanced
quotient. No atlas or analytic structure of the output quotient is an input.

Let `K : Type u` be a complete normed field with ultrametric distance,
`G : Type z` a group, and `H : Subgroup G`. The source is an actual
`Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H` called `X`.
Its arrows contain continuous point maps, monotone chosen chart targets, and
compatible bounded algebra pullbacks. The universes absorb the coset-index
universe into both the point and chart-index universes. Empty source spaces
and empty chart-index types are permitted; no finite-index hypothesis is used.

`localAction` restricts each original action arrow to the same-space
`nonemptyPresentation`. Its identity and multiplication laws follow from
`Hom.nonemptyMap_id` and `Hom.nonemptyMap_comp`. This retains precisely the
original charts whose spectra are nonempty, with their original quotient
algebras and restrictions. It does not assert a chosen-category isomorphism
between a presentation and one obtained by deleting its empty charts.

`component` is the constant family of these presentations over `G ⧸ H`.
`copies` is their constructed topological sigma presentation, and `copy` is
its complete bounded component inclusion. The published representative
correction is

`κ(g,c) = (g • c).out⁻¹ * (g * c.out) ∈ H`,

so `g * c.out = (g • c).out * κ(g,c)` and
`κ(g*k,c) = κ(g,k • c) * κ(k,c)`. `copiesActionMap` reindexes a copy
by `c ↦ g • c` and applies `localAction κ(g,c)` inside it. The projection
lemmas identify the actual point map, chosen chart index, and original bounded
pullback. `copy_action` proves the entire component restriction equation.
Restricting to each copy and using the correction cocycle proves
`copiesActionMap_one` and `copiesActionMap_mul`. The latter states
`a(g*k) = a(k) ≫ a(g)`, with the usual geometric action order.
These compare full chosen arrows, including dependent bounded pullbacks.
They construct `copiesAction` and its actual group of automorphisms
`copiesAutomorphisms`. No topology on `G` or openness of `H` is needed for
this part.

`LocalSpace H X` is the actual original point space with its original topology
and the constructed action `h • x = (X.ρ h).baseMap x`. The action laws are
obtained from the full original categorical laws. For the quotient part,
`G` is a topological group, `H` is open, and the sole additional source
continuity hypothesis is `ContinuousSMul H (LocalSpace H X)` for this specific
action. This hypothesis concerns the input, not the output quotient.
`Space H X` is the published balanced quotient
`TopologicalInduction.Space H (LocalSpace H X)`, with its product-quotient
topology. `copiesHomeomorph` is the actual coset-copies homeomorphism
`(c,x) ↦ [c.out,x]` onto that quotient.

`presentation` transports the entire constructed sigma atlas through this
homeomorphism. Thus the embeddings, local Hausdorff neighborhoods, net,
bounded restrictions, and universal domain factorizations for every presented
affinoid test algebra come from the actual disjoint-union and atlas-transport
constructions. Original positive polyradii, quotient topology, nilpotents, and
empty or nonstrict test spectra are retained. The exact algebra and chart
formulas are `presentation_algebra` and `presentation_chart`:
the chart tagged by `(c,i)` has algebra `X.V.atlas.algebra i.val` and maps
`x` to `[c.out, X.V.atlas.chart i.val x]`.
`presentation_chart_subset_iff` preserves and reflects all original chart
containments within each coset. `presentation_restriction_same` identifies
its actual bounded restriction with the original restriction, including
containment between distinct original charts. Containment in the sigma
construction equates only coset tags, never overlapping original indices.

`copiesIso` is an actual bounded atlas isomorphism with identity chart indices
and bounded identity pullbacks. Conjugation defines `actionMap` on the quotient;
its full identity and multiplication laws give `action` and `automorphisms`.
`copiesIso_equivariant` and `equivariantCopiesIso` retain the full arrows in
the equivariant comparison. The chart-index formula retains the original
correction-action target; `actionMap_pullback` cancels the transport identities
as actual algebra maps to recover `(X.ρ κ(g,c)).pullback i.val`.

The representative equation and the quotient balancing relation prove
`copiesActionMap_realization`. Surjectivity of `copiesHomeomorph` then proves
`actionMap_baseMap`: the transported point map is exactly `x ↦ g • x` on
the original balanced quotient. Joint continuity follows from the published
continuous quotient action, and `continuousAction` packages this exact
categorical realization as a continuous topological action.

The original motivation is Berkovich's unfinished *Etale equivariant sheaves
on p-adic analytic spaces* (1995–1996), Construction 1.1.2, printed/PDF page 2.
The registered folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
with digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
That passage defines the action between copies by `g*g_i = g_j*h`.
The present construction internally derives the complete bounded realization
for supplied overlapping atlases from `AtlasNonemptyCharts`,
`AtlasDisjointUnionTransport`, `AtlasHomeomorph`, and `InducedCharts`, reusing
the published correction cocycle from `GeneralizedAffinoid.InducedAction`.

The source's continuity into the analytic automorphism group remains a
separate comparison: only underlying joint continuity is proved here. This
module does not yet construct the normalized unit, the induction functor or
its universal extension to arbitrary atlas targets. Refinement localization,
the general analytic morphism category, analytic sites and the Harris tower
specialization also remain separate obligations. No algebra-map equality
is inferred from agreement on spectrum points.
