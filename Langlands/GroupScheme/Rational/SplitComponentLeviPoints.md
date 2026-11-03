# Split-component points in the actual standard Levi subgroup

Author: Worker 1507. Module `Langlands.GroupScheme.Rational.SplitComponentLeviPoints`,
namespace `Langlands.GroupScheme`.

This is an internal adapter between published actual group-scheme objects. It
supplies the point map `A(F) → M(F) → standardLeviPoints` used by Renard,
*Représentations des groupes réductifs p-adiques* (9 July 2026), VII.1.1,
printed p. 220 / PDF p. 226, where the split component `A` of a Levi `M` acts on
the normalized Jacquet module. The book takes this action for granted; it states
no separate result about the map. The centrality and continuity proofs below are
derived from published Library definitions. They add no new structural assertion
about reductive groups.

## Setting

`F : Type u` is a field. `G` and `T` are a group scheme and a commutative group
scheme over `Spec F` with `[IsAffineHom G.X.hom]`; `i : T.toGrp ⟶ G`,
`ν : cocharacterLattice T` and `J : Set (characterLattice T)` are the data of the
published `standardLevi i ν J`. The input `j : M ⟶ G` with
`hj : (standardLevi i ν J).IsRepresentedBy j` is a chosen represented Levi.
`a : H ⟶ M` is an arbitrary homomorphism of group schemes; the split-component
case is `H = A.toGrp` with `IsSplitComponent a`. The existence of a represented
Levi or of a split component is not proved here: `j`, `hj` and `a` are inputs.
Everything stays in the single universe `u` of the published group-scheme API.

## Declarations

- `IsSplitComponent.isAffine`: if `a : A.toGrp ⟶ M` is a split component, then
  `A.toGrp.X.left` is affine. A split component is in particular a split subtorus
  (`IsSplitComponent` is the published conjunction of `IsCentralSplitTorus a` and
  maximality). The proof takes the `IsAffineHom` structure of that split torus and
  applies `isAffine_of_isAffineHom`.
- `continuous_rationalPoints_map`: for affine `H` and `M`, `rationalPoints.map a`
  is continuous from `rationalPointTopology F H.X` to `rationalPointTopology F M.X`.
  This is the published `continuous_rationalPointMap F a.hom.hom`.
- `splitComponentLeviPointsMap i ν J j hj a : rationalPoints H →* standardLeviPoints i ν J`
  is `rationalPoints.map a` followed by the published
  `standardLeviRationalPointsEquiv i ν J j hj`. This uses the exact represented-Levi
  witness `hj`. The lemmas `splitComponentLeviPointsMap_val` (ambient value
  `rationalPoints.map j (rationalPoints.map a x)`) and `splitComponentLeviPointsMap_apply`
  (the factorization through `M(F)`) hold by `rfl`.
- `splitComponentLeviPointsMap_eq_standardLeviCentralRationalPointsMap`: for central
  `a` (`IsCentral a`), the map equals the published
  `standardLeviCentralRationalPointsMap i ν J j hj a ha` followed by the inclusion of
  `Subgroup.center (standardLeviPoints i ν J)`. This also holds by `rfl`.
- `splitComponentLeviPointsMap_mem_center` (centrality): for central `a`, every value
  lies in `Subgroup.center (standardLeviPoints i ν J)`. The proof is the membership
  field of the published central point map.
- `IsSplitComponent.splitComponentLeviPointsMap_mem_center`: the same statement for a
  split component, using the centrality field of `IsCentralSplitTorus`.
- `continuous_splitComponentLeviPointsMap` (continuity): under `[TopologicalSpace F]`,
  `[IsAffine G.X.left]` and `[IsAffine H.X.left]`, the map is continuous from
  `rationalPointTopology F H.X` to the published `standardLeviPointTopology i ν J`.
  That topology is induced from `rationalPointTopology F G.X` by the subtype inclusion.
  By `continuous_induced_rng`, it suffices that the composite with the inclusion is
  continuous. That composite is the point map of `a ≫ j`, which is continuous by
  `continuous_rationalPointMap F (a ≫ j).hom.hom`.

## Topology comparison not used

The continuity proof never uses `StandardLeviPointTopologyComparison`, which the
Library declares separately as an unproved target. Nor does it use the published
`standardLeviRationalPointsHomeomorph`, which needs `j` to be a closed immersion.
The proof needs no closed-immersion, local-compactness, separation or reductivity
premise. Continuity into the canonical topology of `M(F)` is
`continuous_rationalPoints_map`. Continuity into the subgroup topology inherited
from `G(F)` is `continuous_splitComponentLeviPointsMap`. Both topologies are
installed only locally, through `letI` in the statements.

## Specialization

For the standard rational-point family (`Langlands.Aubert.General.RationalPointFamily`),
`levi i ν I` is the abbreviation `standardLeviPoints i ν (rootSet i ν I)`, and that
family's local `pointTopology` is `rationalPointTopology k G.X`. The module
`Langlands.Representation.Exponents.NormalizedJacquetSplitComponent` applies the
declarations above with `J = rootSet i ν I`.

## Not covered

This file proves nothing about the existence or uniqueness of split components
or represented Levis. It does not prove the topology comparison on `M(F)`, any
properness or closedness of the image, or the compactness of `Z(M)/A_M`.
