# Special-fibre maximality of a common integral split torus

These internal results are derived from the Library's generic closedness theorem for split
tori and its Henselian split-rank specialization theorem. They isolate the target
special-fibre maximality argument needed in KP Axiom 4.1.22(3).

`RelativeComponentModelHom.mapIntegralTorus` transports supplied integral torus
data along the neutral part of a compatible model morphism. Its torus and generic
identification are unchanged, and its inclusion is the composite integral map.
The two generic compatibility squares give the new compatibility square.
The construction alone asserts neither closedness nor splitting nor maximality.

`IntegralModel.isClosedSubgroup_of_split_generic` expresses an arbitrary split
integral torus in standard split coordinates. Precomposing its map to the model
with that isomorphism reduces closedness to
`SplitTorusClosure.isClosedSubgroup_of_genericTorusMap`. Closedness is then
transported back through the inverse isomorphism.

`RelativeComponentModelHom.isMaximalSplitTorus_targetTorusInclusion` assumes a
noetherian Henselian integral base, a connected reductive generic group, a model
morphism, and a split integral torus with maximal generic fibre. The compatibility
of the generic identifications identifies the composite integral map's generic
fibre with the given maximal split torus. The first lemma makes that integral map
closed. The theorem `isMaximalSplitTorus_residue_of_generic` then gives maximality
in the target special fibre. Base change preserves composition, so this is the
specified `targetTorusInclusion`.

This result does not assert maximality in a reductive quotient or a Lie-weight
formula. It uses neither a facet characterization nor maximality in the source
special fibre.

Source-isomorphism transport of split maximality uses the existing
`IsMaximalSplitTorus.iso_comp` from
[UnipotentQuotientMaximalSplit](../../GroupScheme/Torus/UnipotentQuotientMaximalSplit.md).
