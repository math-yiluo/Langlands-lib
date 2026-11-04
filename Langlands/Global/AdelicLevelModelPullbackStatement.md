# Pullbacks of actual arithmetic-level model points

`Langlands.Global.AdelicLevelModelPullbackStatement` is the conjunction of
`CurvePlaceLevelModelPullbackStatement` and
`NumberFieldLevelModelPullbackStatement`, in arbitrary common universe `u`.
It asserts preservation of relative pullbacks by actual points at one
arithmetic level, with the already constructed level topology.

The curve clause uses the actual outside-`S` integer subring
`curvePlaceSIntegers k F S` and the actual restricted-product subring
`curvePlaceAdeleLevel k F S`. It quantifies over fields `k` and `F`, their
specified algebra action, and any finite set of actual curve places,
including the empty set. No perfectness, rational-function-field
structure or separability hypothesis is imposed.

The number-field clause uses the actual `S`-integer subring of an
arbitrary number field and `numberFieldAdeleLevel K S`, which includes
every infinite completion, the finite completions in `S`, and the
completed valuation rings outside `S`.

In both clauses, `X`, `Y` and `Z` are arbitrary schemes over the stated
integer base. For arbitrary maps `f : X ⟶ Z`, `g : Y ⟶ Z` and an actual
limiting pullback cone `c`, the asserted homeomorphism is the existing
map `affineSchemePullbackPointComparison`. Despite its historical name,
that map has no affineness premises. It sends an actual point `p` to
`(p ≫ c.fst, p ≫ c.snd)`, with equality of the two composites into `Z`.
The target carries the subspace topology from the product of the two
existing level point topologies. Compatibility is equality of actual
scheme morphisms; no coordinatewise substitute is used.

Each level topology is the initial topology for coefficient restriction
to all actual local factors followed by the actual base-change point
equivalence. The topology on each local model is the affine-chart final
scheme point topology. These are the existing constructions from
`AdelicLevelModelTopology`; the statement supplies neither an arbitrary
topology nor an assumed topological pullback package.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Printed p.8, the paragraph after the proof of Theorem 3.6, states that
the level topology preserves fiber products for finite-type models
over global-field integer bases. Theorem 3.6 and (3.6.1) on printed
pp.6–8 construct that level topology from actual local-model points.

The arbitrary-scheme and arbitrary-curve-field scope here is a derived
extension. Its route uses preservation of limits by actual scalar base
change and by relative morphism sets. Each actual local value ring is
local and topological with open units, so the local scheme-point
pullback comparison applies without finiteness or separatedness.
Initial topologies along the local-model maps preserve this comparison:
continuity in both directions can be tested on every local factor.
This requires no bijectivity of the local-model product map, hence no
quasi-compactness or quasi-separatedness assumption on the models, and
no finite residue fields or local compactness.

This pair defines the exact proposition target; it does not prove it.
Preservation of pullbacks for fixed-model final topologies or for
generic-fiber adelic topologies is a separate obligation.
