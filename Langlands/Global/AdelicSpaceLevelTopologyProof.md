# Topology of adelic-level points of separated algebraic spaces

Author: Worker 105.

Proof of `Langlands.Global.AdelicSpaceLevelTopologyStatement.{u}`: Conrad's claims on printed
p.17 of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
for global fields of both characteristics. The entry theorem is `adelicSpaceLevelTopology`; its
components are `numberFieldSpaceLevelTopology_proof` and `curvePlaceSpaceLevelTopology_proof`.

The target says: let `X` be a separated algebraic space of finite type over the `S`-integers of
a number field (resp. a global function field with `S` nonempty). Then the topology on its
adelic-level points is locally compact and Hausdorff. Every change of level `S ⊆ T`, into the
level points of the base change of `X` to the `T`-integers, is an open embedding.

## Route

The level topology (`numberFieldSpaceLevelTopology`, `curvePlaceSpaceLevelTopology`) is induced
along the coordinate map to the product of the factor topologies.

- **Factors.** Each completion is a henselian valued field whose norm induces its topology
  (`AdelicSpaceLocalFields`). At an infinite place and at a place of `S`, the factor is
  homeomorphic to the étale-chart topology on `X_{F_v}(F_v)`. It is Hausdorff and locally
  compact by Proposition 5.4. Away from `S`, the factor `X(O_v)` embeds in `X_{F_v}(F_v)` with
  open, quasi-compact image by Corollary 5.7 over the `S`-integers (`RelativeIntegralPoints`).
  So it is compact and Hausdorff.
- **Locally compact and Hausdorff.** Proposition 5.2 (`numberFieldSpaceLevelPoints`,
  `curvePlaceSpaceLevelPoints`) makes the coordinate map bijective, hence a homeomorphism onto
  the product. All but finitely many factors are compact
  (`locallyCompactSpace_coordinatePointTopology`, `t2Space_coordinatePointTopology`).
- **Change of level.** The transition is change of coefficients along the level inclusion,
  followed by the point identification of the base change (`transition_eq`,
  `curve_transition_eq`). The abstract criterion `isOpenEmbedding_levelChange` applies:
  - Every composite field map of one level occurs in the other, with the same field and the same
    algebra structure up to definitional equality (`matching₁`, `matching₂` and their curve
    versions).
  - The source is Hausdorff.
  - The image of the `S`-level in the `T`-level is open (`numberField_isOpen_range`,
    `curve_isOpen_range`). It consists of the points whose coordinates at the finitely many
    places of `T` outside `S` come from the completed integers. One inclusion is direct. For
    the other, Proposition 5.2 at level `S` assembles a preimage, and the injectivity of the
    `T`-coordinates (`coordT_injective`) identifies its image. Openness follows from
    Corollary 5.7.

Over the `S`-integers, the `T`-level ring, its factors and its fields carry the restricted
algebra structures (`algLevel`, `algFactor`, `algField` and the curve versions), made local
instances under `Fact (S ⊆ T)`.

## Declarations

Namespace `Langlands.Global.AdelicSpaceLevelTopologyProof`:

- Number fields: `finiteCompletion_locallyCompactSpace`, `numberField_factor`,
  `numberField_integer`, `numberField_locallyCompact_t2`; `algST`, `algLevel`, `algFactor`,
  `algField`, `towerLevel`, `towerFactor`, `towerField`, `levelAlg`, `transition_eq`,
  `coordT_injective`, `matching₁`, `matching₂`, `numberField_isOpen_range`,
  `numberField_transition`.
- Function fields: `curve_factor`, `curve_integer`, `curve_locallyCompact_t2`; `curveAlgST`,
  `curveAlgLevel`, `curveAlgFactor`, `curveAlgField`, `curveTowerLevel`, `curveTowerFactor`,
  `curveTowerField`, `curveLevelAlg`, `curve_transition_eq`, `curve_coordT_injective`,
  `curve_matching₁`, `curve_matching₂`, `curve_isOpen_range`, `curve_transition`.

Namespace `Langlands.Global`:

- `numberFieldSpaceLevelTopology_proof : NumberFieldSpaceLevelTopologyStatement.{u}`.
- `curvePlaceSpaceLevelTopology_proof : CurvePlaceSpaceLevelTopologyStatement.{u}`.
- `adelicSpaceLevelTopology : AdelicSpaceLevelTopologyStatement.{u}`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, the paragraph after
  Corollary 5.7 on printed p.17, with Proposition 5.2 (pp.13–14), Proposition 5.4 (pp.14–16) and
  Corollary 5.7 (pp.16–17).
