# Properties of the coordinate point topology

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claims on adelic levels
(`Langlands.Global.AdelicSpaceLevelTopologyStatement`). It contains no statement from the
literature. The topology `coordinatePointTopology` on `X(A)` is induced along the coordinate map
`X(A) → ∏ X(R i)` from the product of the factor topologies `fieldValuedPointTopology`. Each
factor topology is induced from the étale-chart topology of `X_{L i}(L i)` along
`fieldValuedPointMap`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointTopologyFacts`.

General topology:

- `iInf_eq_iInf`: two infima of topologies agree when each member of either family occurs in the
  other.
- `induced_comp_isHomeomorph`: composing with a homeomorphism does not change an induced
  topology.

Factors:

- `fieldValuedPointMap_comp`: the field-valued point map along a composite.
- `fieldValuedPointMap_bijective`, `isHomeomorph_fieldValuedPointMap`: along a bijective field
  map the factor is homeomorphic to the étale-chart topology.
- `t2Space_fieldValuedPointTopology`: an injective field-valued point map into a Hausdorff space
  gives a Hausdorff factor.
- `compactSpace_fieldValuedPointTopology`: a quasi-compact image gives a compact factor.

Coordinates:

- `coordinatePointTopology_eq_iInf`: the coordinate topology is the infimum of the topologies
  induced by the composite maps `X(A) → X_{L i}(L i)`.
- `isHomeomorph_coordinatePointMap`: with a bijective coordinate map, it is a homeomorphism.
- `t2Space_coordinatePointTopology`: Hausdorff when the coordinate map is injective and the
  factors are Hausdorff.
- `locallyCompactSpace_coordinatePointTopology`: locally compact when the coordinate map is
  bijective, the factors are locally compact and all factors outside a finite set are compact.
  The product splits as a finite product times a product of compact spaces
  (`Homeomorph.piEquivPiSubtypeProd`).

Change of base ring along `C → C'`:

- `towerIso_fieldValuedPointMap`, `fieldValuedPointTopology_baseChange`: the factor topology of
  the base change to `C'` is induced from the factor topology of `X` along the point
  identification.
- `restrictedFieldMap`, `restrictedTopology`, `coordinatePointTopology_baseChange`: the
  coordinate topology of the base change on `X_{C'}(A')` corresponds to the topology on the
  `C`-points `X(A')` induced by the composite field maps viewed over `C`.
- `continuous_restrictedFieldMap`: each such field map is continuous for it.
- `isOpenEmbedding_levelChange`: **abstract change of level**. Let `t : A →ₐ[C] A'`, with
  coordinate data on both sides. Suppose every composite field map of each side, precomposed
  with `t` on the target side, occurs on the other side. Suppose also that the source is T0 and
  that the image of `X(A) → X(A')` is open for the restricted topology. Then
  `x ↦ (baseChangeRingPointsEquiv C C' A' X).symm (changeRing t x)` is an open embedding for the
  coordinate topologies.
