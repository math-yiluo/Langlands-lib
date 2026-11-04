# Functoriality of actual full-adele model point topologies

`Langlands.Global.AdelicFixedModelFunctorialityStatement` asserts that
postcomposition with an actual arithmetic model morphism is continuous on
actual full-adele points. Its two clauses cover the curve-place construction
and the full number-field construction.

The source and target have their independently defined final topologies
`curvePlaceFixedModelAdelePointTopology` or
`numberFieldFixedModelAdelePointTopology`. Each is final from the original
arithmetic stages over the fixed initial integer ring. At a stage T, the
topology comes from the global local-factor topology of the actual model
pulled back to the outside-T integers. Both full point types retain the
original outside-S scalar action. The map is the literal composition
`p ≫ f` in the category of schemes over that base.

## Scope and provenance

This is a derived prerequisite for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed p.8 after the proof of
Theorem 3.6, and the functorial final-topology construction at the start of
section 4 on printed p.9. The finite-stage continuity assertion, together
with the universal property of the final topology, gives the present
fixed-model assertion.

No finite-type, quasi-compactness, quasi-separatedness, separatedness or
affineness hypothesis is imposed on the models. The curve-place clause
allows arbitrary fields k and F with a k-algebra structure; no finite
constant field or function-field presentation is needed. An empty S and an
arbitrary common universe are allowed. This broader scope is a derived
extension of Conrad's finite-type global-field application: continuity of
the local point maps and the definition of the final topology require none
of those extra hypotheses. No assertion that the point stages form a
bijective presentation is used. The number-field clause retains every
infinite factor of the full adele ring.

The statement compares models over one fixed integer base. It does not yet
assert independence of arbitrary spreads or identify these points with
points of the generic fiber. It is a proposition target; its proof is a
separate obligation.
