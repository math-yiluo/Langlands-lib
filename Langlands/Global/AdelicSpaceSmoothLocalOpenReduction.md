# Local smooth openness and adelic factors of algebraic spaces

Author: Worker 109.

This is a derived reduction for Task 5254. It does not prove
`CompleteFieldSmoothSpacePointOpenStatement` or
`AdelicSpaceSpreadSmoothOpenStatement`.

The module uses the actual `RingPoints`, `baseChangeMap` and
`fieldValuedPointTopology` of the published Library. It first proves
naturality of `fieldValuedPointMap` by the naturality of the base-change
point equivalence and change of coefficients. If a coefficient map is
bijective, the two field-valued point maps are homeomorphisms, so openness
of the generic-fibre map transfers to the coefficient point map.

For a henselian subring `O` of a nontrivially normed field `L` whose
underlying set is the closed unit ball, and separated spaces locally of
finite type over an arbitrary coefficient ring `C`, the map
`X(O) → X_L(L)` is inducing and has open image by
`RelativeIntegralPoints.isOpen_range_fieldValuedPointMap`. For the target
it is also injective by separatedness. Therefore it is an open embedding.
`integerFactorHomeomorphRange` bundles this embedding as a homeomorphism
onto its open image, with the original integral point map as its forward
function after forgetting the range subtype.
The naturality square identifies its composite with the map on
`O`-points with the composite of the generic-fibre map and the open source
coefficient map. Mathlib's `IsOpenEmbedding.isOpenMap_iff` then proves
openness on `O`-points. This step assumes the generic-fibre map is open;
it does not require completeness, smoothness or any surjectivity.

The smooth corollaries assume
`CompleteFieldSmoothSpacePointOpenStatement` explicitly. They apply that
proposition to the generic fibres, using the published preservation of
separatedness, local finite type and smoothness under base change, and
then use the field and integer reductions. They retain arbitrary universe
`u`, arbitrary characteristic and the actual coefficient actions.

These are formal consequences of the cited published definitions and
theorems. The implementation follows the coefficient-square argument
already used for schemes in `AdelicSmoothLocalOpen`, adapted to the
different algebraic-space point types and their induced topologies.

The `curvePlaceSpaceFactor_isOpenMap_of_smooth` and
`numberFieldSpaceFactor_isOpenMap_of_smooth` corollaries apply these
reductions at every actual factor of the adelic level. They use the
nontrivial norms and henselian unit-ball descriptions from
`AdelicSpaceLocalFields`. The given topologies and coefficient actions
are preserved; all infinite number-field factors are included. These
corollaries need only separatedness and local finite type for the models.

For separated models of finite type, the `…Level_isOpenMap_of_smooth`
and `…Stage_isOpenMap_of_smooth` lemmas combine factor openness with the
published actual level and stage reductions in
`AdelicSpaceModelOpenReduction`. The stage corollaries base change the
model morphism to the enlarged ring of integers, preserving smoothness.
Both level and stage results retain the explicit hypothesis that the
point maps of all but finitely many factors are surjective. In the
function-field case they retain the nonempty initial set of places.

The missing local smooth-openness theorem is tracked by Task 5359,
`f1585194-c81c-4c5b-a346-e4e15f1a05ad`. Compatible arithmetic models,
almost-all component surjectivity, source-stage coverage, open target
stage maps and independence of models remain obligations of the adelic
argument or its existing prerequisite tasks.
