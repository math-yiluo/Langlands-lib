# Nonempty-chart atlas actions with jointly continuous point actions

Author: Worker 56. Namespace: `Langlands.Analytic`.

Let `K` be a complete normed ultrametric field and `M` a monoid equipped
with a topology. `PointContinuousNonemptyAtlasAction K M` is the full
subcategory of actual categorical actions on supplied
`AffinoidAtlasPresentation K` objects satisfying two explicit conditions:
every original chart has nonempty bounded multiplicative spectrum, and
the map `(m,x) ↦ (X.ρ m).baseMap x` on the original point space is jointly
continuous. No continuity of multiplication on `M` is required for these
constructions. Presentation, point-space, chart-index and action-parameter
universes remain independent.

All morphisms are the original complete equivariant chosen atlas arrows,
including continuous point maps, chosen target indices and compatible
bounded algebra pullbacks. `inclusion` is full and faithful. `toNonempty`
forgets the continuity condition and retains the exact nonempty-chart
action. `toNonempty_inclusion` identifies its composite with the original
inclusion.

`realization` sends the precise categorical point action and each original
point map to Mathlib's category `ContAction TopCat M`. Its continuity is
the stated input condition, via `Action.isContinuous_def`; it introduces
no different topology or action. The projection lemmas expose the exact
underlying space and continuous map.

`normalize` lifts the constructed same-space nonempty-chart normalization
to this continuous category: both the topology and point action are
unchanged, so joint continuity is inherited. `normalizationIso` uses the
existing conditional bounded action isomorphism, whose inverse exists
because every original chart satisfies the explicit spectrum condition.
The full-arrow normalization naturality proves `normalizationNatIso`
from this functor to the identity.

For any topological monoid type `N` and continuous monoid homomorphism
`φ : N →ₜ* M`, `restrict φ` precomposes the action parameter. Joint
continuity follows by composing the original joint action with
`(n,x) ↦ (φ n,x)`. The original presentation, every action operator at
`φ n`, and every complete arrow are retained exactly. The final functor
equality identifies restriction after forgetting continuity with the
existing restriction on nonempty-chart actions.

The provenance is internal packaging of `NonemptyAtlasActions`,
the existing chosen-atlas space functor, and Mathlib's full subcategory
and continuous-action constructions. The normalization inverse and its
naturality are reused from the actual bounded normalization; equality of
bounded maps is never inferred from agreement on spectrum points.
The condition concerns joint continuity on points. Continuity into an
analytic automorphism topology, refinement localization, analytic sites,
and Harris tower specialization remain separate obligations. Empty
spaces with no chart indices and overlapping supplied charts are allowed.
