# Regular-atlas assembly and the intrinsic family criterion: exact targets

These proposition definitions isolate the analytic consequences of a
`RegularAtlas k X d` on an affine scheme's actual points. No algebraic
smoothness hypothesis is used in these targets: the separate
`regularChartExistenceStatement` must produce the atlas from algebraic
smoothness.

`regularAtlasManifoldStatement k X d` states that every such atlas makes
its existing charted space a real `C∞` manifold, modeled on `Fin d → k`.
The charted space was constructed from the atlas's open partial
homeomorphisms for the existing regular-evaluation topology. No target
topology is replaced.

`regularAtlasFamilyCriterionStatement k X d` quantifies over every
regular atlas and every source real smooth manifold, with its normed
model `E`, chart model `H`, model with corners `I`, topology, charted
space and `IsManifold I ∞ M` hypothesis explicit. For every map
`f : M → RingPoint k X k`, it equates actual `ContMDiff` into the
atlas's charted space with `RegularSmooth I f`, meaning smoothness of
every global regular-function value in `k` as a real normed space.
The source universes are arbitrary.

`regularAtlasComparisonStatement` is the conjunction of these two
obligations. All three declarations return `Prop`; none is a theorem,
axiom, or instance. The family criterion concerns the charted space
given by the atlas and is not the definition of smoothness into it.

The provenance is internal, derived from the explicit rational-coordinate
and inverse-evaluation fields of `RegularChart` and Mathlib's definitions
of `IsManifold` and `ContMDiff`. The intended proof checks changes of
coordinates using smooth quotients of inverse-chart regular evaluations.
For the forward family implication it proves smoothness of global
regular evaluations on inverse charts. For the reverse implication it
first uses the published evaluation-topology criterion to obtain
continuity and then uses the rational forward coordinates locally.
These proof obligations remain open until a separate proof task is
accepted and published.
