# Morphisms on coordinate point topologies

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claims on adelic points
(`Langlands.Global.AdelicSpacePointTopologyStatement`). It treats morphisms on the topologies
of the adelic levels from `Langlands.Global.AdelicSpaceLevelTopology`:
- `fieldValuedPointTopology`: induced along `X(A) → X_L(L)` from the étale-chart topology;
- `coordinatePointTopology`: induced along `X(A) → ∏ᵢ X(Rᵢ)` from the product of factor
  topologies.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps`. Here `f : X → Y` is
a morphism of algebraic spaces over `Spec C`.

- `isClosedImmersion_baseChangeMap`: base change keeps closed immersions
  (`relative_restrictPresheaf_map`).
- `finiteTypeOverRing_baseChange`: base change keeps `FiniteTypeOverRing`.
- `fieldValuedPointMap_map`: the field-valued point map along `φ : A →ₐ[C] L` is natural.
  It carries `f` to the base change of `f` to `L`.

For a henselian valued field `K` (`IsHenselianValuedField`) with a `C`-algebra structure:

- `continuous_fieldValued`: if `Y` is separated of finite type, `f` is continuous for the
  field-valued topologies. This follows from naturality and `continuous_ringPointsMap`.
- `isClosedEmbedding_fieldValued`: if `X` and `Y` are separated of finite type, `f` is a closed
  immersion and `φ : A → K` is injective, then `f` is a closed embedding for the field-valued
  topologies.
  - The base change of `f` to `K` is a closed embedding (`isClosedEmbedding_ringPointsMap`).
  - Inducing follows from naturality, and injectivity from `ClosedImmersionPoints.map_injective`.
  - The image of `X(A)` is the preimage of the image of `X_K(K)`, by
    `ClosedImmersionPoints.exists_changeRing_eq` applied to `φ`. Hence it is closed.

For families `π i : A → R i` and `φ i : R i → L i`:

- `coordinatePointMap_map`: the coordinate map is natural.
- `continuous_coordinate`: if `f` is continuous on every factor, it is continuous for the
  coordinate topologies.
- `isClosedEmbedding_coordinate`: suppose the coordinate maps of `X` and `Y` are bijective, as
  in Proposition 5.2. Then the coordinate maps are homeomorphisms onto the products
  (`isHomeomorph_coordinatePointMap`). So if `f` is a closed embedding on every factor, it is
  one for the coordinate topologies (`IsClosedEmbedding.piMap`).
