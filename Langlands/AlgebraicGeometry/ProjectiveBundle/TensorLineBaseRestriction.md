# Line chart restriction scalars

This derived unit works over an arbitrary scheme `S : Scheme.{u}`, a module
sheaf `N`, and opens `U ≤ V`. Its inputs are actual trivializations of the
restrictions of `N` to `U` and `V`. No global trivialization is required.

`openLineIso` expresses a restriction trivialization as an isomorphism from
actual pullback along the open immersion to the structure module.
`lineCoordinates_openSection` identifies its value on the actual open section
with the original-open line coordinates, transported along `U.topIso.inv`.
`lineCoordinates_restrict` proves that original-open coordinates commute with
section restriction within a chart.

`openLineTransitionUnit tV tU h` is the previously constructed coordinate
comparison unit on `U`, transported to global functions on `U.toScheme`.
Its orientation is smaller-chart coordinates equal this unit times
larger-chart coordinates. `openLineRestrictionIso tV h` is the pullback of
the larger actual trivialization along `S.homOfLE h`, followed by the canonical
pullback comparison for the structure module.

`openLineIso_restrict` proves the isomorphism equation: the larger
trivialization restricted to `U`, followed by the unit automorphism for
`openLineTransitionUnit`, equals `openPullbackIso N h` followed by the smaller
actual trivialization. Equivalently, the restricted larger trivialization
contains the inverse of the original coordinate transition scalar.

The coordinate bridge cancels the restriction-to-pullback comparison and uses
naturality of the given trivialization and the existing original-open chart
coordinate formula. The restriction equation is checked on the pulled-back
basis section of the larger chart. Its larger-chart coordinate is one. The
canonical section-pullback formulas show that the restricted trivialization
also sends it to one. Precomposing by the inverse trivialization reduces the
morphism equation to endomorphisms of the structure module, where equality is
determined by the global value at one. The smaller coordinate is precisely the
comparison unit by the existing coordinate-change and restriction formulas.

The provenance is derived from `TensorFrameOverlap`, the coordinate formulas
of `TensorContractionTransport` and `LineBundleSectionClearingProof`, the actual
section pullback comparisons of `EvaluationRestriction` and
`SectionPullbackBridge`, and the structure-endomorphism extensionality of
`StructureUnitScalars`. No additional geometric assertion or literature premise
is introduced. Pulling this equation to the projective charts, tensor scalar
cancellation, global gluing and ordinary representability remain separate work.
