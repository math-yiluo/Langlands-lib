# Actual root-point Lie coordinates under field extension

This internal comparison specializes the actual vector coordinate and tangent
base-change constructions to intrinsic root subgroups. It is derived from
`RootSubgroupBaseChange`, `RootPointLieNaturality`, `VectorPointLieBaseChange`
and the published field-extension comparison for actual root support. It has
no independent literature claim.

`IsWeightVectorCoordinates.baseChange` proves that natural coordinates of a
single actual character weight retain that weight after field extension.
The affine coordinates and their naturality are transported by the actual
scheme-pullback point comparison. Its compatibility with actions and character
values proves the weight assertion on every test scheme.

`rootSubgroup_isRepresentedBy_baseChange` applies the actual root-functor
base-change equality and base change of a representing inclusion.
`subgroupAction_baseChangePointsEquiv_act` identifies its conjugation action
with the original representative's action under the point comparison.
Postcomposing with the monomorphic inclusion proves that identity.
`IsWeightVectorCoordinates.rootBaseChange` consequently preserves weight
coordinates for the actual root action.

For an affine smooth ambient group and a split acting torus,
`HasNoHigherRoots.baseChange` preserves the absence of higher positive roots.
This follows by reflecting actual root membership along field extension and
the character map's compatibility with positive integer multiples.

For any affine representative of a nonzero root with no higher positive roots,
`rootVectorPointLieEquiv_baseChange` compares its point-to-Lie maps over every
compatible coefficient algebra, including nonreduced algebras. Coordinates
chosen independently after field extension and coordinates transported from
the original field have the same nonzero character weight. Uniqueness of the
weight scalar structure identifies their point-to-Lie maps. The established
vector point-to-Lie base-change identity then gives the asserted commuting
square. No compatibility of the independent coordinate choices is assumed.

`rootVectorPointLieBaseChangeEquiv` transports the original representative's
point-to-Lie additive equivalence through the actual affine-point and tangent
pullback comparisons. `rootVectorPointLieBaseChangeEquiv_eq` identifies this
transported equivalence with the independently constructed equivalence over
the extended field by applying the preceding commuting-square identity.
