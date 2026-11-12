# Universal closedness of target families after arbitrary scheme base change

This internal unit proves that the actual target family tests universal
closedness after any change of scheme base. It retains arbitrary schemes,
algebraic spaces and morphisms. Only the target chart is required to be etale
and surjective for the final equivalence; no affine, finite-presentation or
representability hypothesis on the original morphism is added.

`fibreSchemeProjection` sends an actual presheaf fibre point to the ordinary
point of its scheme test, using `schemePointsTo` after the fibre projection.
The represented scheme point homeomorphism proves that this map is closed
exactly when the original fibre point projection is closed. Forgetting a
recorded scheme base fixes the underlying scheme point. Together with the
published fibre-restriction projection identity, this proves the ordinary
projection identity for fibre restriction.

`structuralBaseChangeFibreHomeomorph_schemeProjection` tracks projection through
the existing structural base-change fibre homeomorphism. Its four components
are the terminal-target arrow comparison, a pullback equality comparison, the
fibre-restriction homeomorphism and the equality of the recovered test. Each
preserves the ordinary point of the test scheme.

`AffineTargetFamily.testFibreHomeomorph` combines the recovered-test
rebase homeomorphism with the iterated target-chart pullback isomorphism.
Its projection identity follows from those components and from the fact that
the recovered test homeomorphism fixes the ordinary test point.
`baseChangeSchemeTestFibreHomeomorph` then combines the structural base-change
comparison, this scheme-test comparison, the map/pullback adjunction's original
test identity and inverse fibre restriction. Its projection lemma identifies
the ordinary test-scheme projections on the two actual fibres.

Finally, `AffineTargetFamily.isUniversallyClosedMorphism_baseChange_iff` proves
that universal closedness of `baseChangeMap g f` is equivalent to universal
closedness of the structural map of the target family after base change along
the actual target-chart pullback projection. In the forward direction, every
test of the structural family gives a represented test of the changed original
morphism, and the projection-preserving fibre homeomorphism transfers
closedness. Conversely, the published etale target-atlas criterion reduces to
tests over the changed chart. The same homeomorphism transfers closedness to
the changed original fibre, and the iterated-pullback projection comparison
returns it to the target-chart pullback fibre.

The provenance is internal: the published actual affine target families,
structural and restriction fibre homeomorphisms, recovered-test rebase
comparisons, the scheme point homeomorphism and the universal-closedness
target-atlas criterion. Integration follows `SchemeTargetUniversallyClosed`.
The result does not assume or prove eventual properness. Descent of a chosen
proper scheme cover and its map, the cover-existence prerequisite, and the
full eight-property limit theorem remain separate obligations.

The family-test homeomorphism is the existing
`AffineTargetFamily.testFibreHomeomorph` from `AffineTargetFamilyBaseChange.lean`.
This module adds its ordinary scheme-projection compatibility.
