# Affine pinned étale charts of a reductive group scheme

This internal construction turns the proved `etaleLocalSplitReductive` into
actual pinned affine charts. It introduces no new splitting hypothesis.

`AffinePinnedChart G` supplies an `AffinePinnedModel`, an étale map from its
base to the base of `G`, and an actual isomorphism from the pullback of `G` to
the model group. `AffinePinnedChart.exists_over` proves that every point of
the base of a reductive group lies in such a chart.

The proof applies the published étale local splitting theorem at the point.
Its fibrewise root datum is finite and reduced, so the published
`RootDatumBase.base` chooses a base on its integral coordinate lattices.
The theorem supplies a trivialization of every root Lie line. Inverting the
trivializations on the simple roots supplies the pinning fields of the
model. The model group is exactly the pullback group obtained from the
splitting theorem, so the chart isomorphism is the identity.

`AffinePinnedAtlas G` chooses one chart for each base point, with a
distinguished point mapping to it. `ofReductive` constructs such an atlas
from reductivity by classical choice. `cover` is the corresponding actual
étale covering family. `space` is its scheme coproduct, and `projection`
is the coproduct of the chart maps. This morphism is étale because étaleness
is local at the source, and it is surjective by the distinguished points.
There is no quasi-compactness, connectedness, or nonemptiness hypothesis on
the base. On an empty base the indexed coproduct is empty.

The provenance is internal: the mathematical existence input is the proved
Library étale local splitting theorem, combined with the proved integral
root-datum base construction. The module supplies charts and their single
covering morphism; it does not construct corrected transitions, descend a
group scheme, or prove existence of a quasi-split inner form.
