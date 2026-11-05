# Continuity of actual full-adele model postcomposition

`Langlands.Global.adelicFixedModelFunctoriality` proves exactly
`Langlands.Global.AdelicFixedModelFunctorialityStatement`.
`curvePlaceFixedModelAdele_continuous` and
`numberFieldFixedModelAdele_continuous` prove its two clauses.

The result concerns literal composition of actual relative scheme maps over
one original outside-S integer ring. The source and target have the
independently defined final arithmetic topologies. It supports Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
the functoriality discussion on printed pp.8–9.

The theorem retains the target's arbitrary-model scope: neither finite type
nor quasi-compactness nor separation nor affineness is required. Every stage
and the full adele ring keep the original outside-S scalar action. The curve-place construction
allows arbitrary fields and an algebra structure, without a function-field
presentation or finite constants. S may be empty and the common universe
is arbitrary. All infinite number-field factors are retained. These
extensions use continuity and the final topology, with no assertion of a
bijective presentation by stages.

## Implemented proof

For each fixed-base stage T, the proof first specializes
`ringPointBaseChangeEquiv_natural` to the original arithmetic scalar
actions. This identifies postcomposition by a model morphism with
postcomposition by its actual pullback over the outside-T integers.
The scalar tower is proved from the literal integer inclusion and the
original diagonal action.

The fixed-model stage comparison is already a homeomorphism.
Conjugating the continuous pulled-back model map from
`adelicLevelModelFunctoriality` by the two stage homeomorphisms gives a
continuous stage map. The naturality identity and the inverse law of the
point equivalence identify its underlying function with `p ≫ f`.

To prove continuity on full-adele points, the proof uses
`ringPointCoconeTopology_continuous_iff`. At each stage it composes the
continuous stage postcomposition map with the continuous insertion into
the target full-point space. Associativity of actual scheme-map
composition identifies this composite with the restriction of full-point
postcomposition. The universal property of the final topology completes
the argument. The two arithmetic branches use the same proof.

As immediate corollaries, `curvePlaceFixedModelIsoHomeomorph` and
`numberFieldFixedModelIsoHomeomorph` construct homeomorphisms induced by
actual model isomorphisms. Their forward and inverse functions are
postcomposition with the isomorphism and its inverse; the categorical
inverse identities give the equivalence laws, and the proved continuity
theorem supplies continuity in both directions.

This unit does not assert independence of arbitrary spreads, initial-set
independence or identification with generic-fiber points.
