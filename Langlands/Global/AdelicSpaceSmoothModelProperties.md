# Automatic properties of the smooth connected-fibre model

Author: Worker 109. This internal supporting unit supplies three remaining
morphism predicates for the actual models constructed in
`AdelicSpaceSmoothModelGeometry`. It uses the published point quotient,
relative diagonal and compact atlas interfaces, without a new external
mathematical input.

A morphism whose source is separated over the base is separated. The absolute
diagonal factors as the relative diagonal followed by the monomorphism from
the kernel pair into the product of the source with itself. The relative
closed-immersion property is stable under base change, so Mathlib's
cancellation along a monomorphism applies to this factorization.

The existing `HasGeometricallyConnectedFibres` predicate includes nonemptiness:
each field-valued target test has a connected and nonempty fibre point space.
Represent a target point by its field and section, and choose a point of this
fibre. Points of its test field spectrum form a singleton, by the published
comparison with scheme points. The pullback equation therefore shows that the
first projection of the chosen fibre point maps to the original target point.
This proves actual point-surjectivity, the definition of
`IsSurjectiveMorphism`; no rational point over the original field is asserted.

Over an affine base, the previously published
`isQuasiCompactMorphism_of_atlas` supplies quasi-compactness from a compact
structural source atlas and a quasi-separated target. Combining this with the
two implications above gives `smoothConnectedModel_morphismProperties`.
Its hypotheses do not require smoothness: the name records its intended use.

`AuxiliaryMorphismGeometry` bundles separatedness, quasi-compactness and actual
point-surjectivity of an arrow. The definition
`SmoothConnectedStageModel.auxiliaryGeometry` constructs this bundle by the
proved implications; it accepts no additional geometric hypothesis. The theorem
`SmoothConnectedStageModel.morphismProperties` also exposes their conjunction for
every constructed stage model. Its source has a finite-presentation compact
atlas and is separated; its target is separated and hence quasi-separated;
its map has nonempty geometrically connected fibres. Thus its map is
separated, quasi-compact and surjective, with none of those three predicates
added as a hypothesis. This applies to both arithmetic branches through the
same actual model construction.

Relative dimensions, uniform Lang-Weil, and the final adelic openness theorem
remain separate obligations. No premise or conclusion of those statements is
changed by this unit.
