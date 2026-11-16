# Split integral-torus data for the full supplied model

This internal derived interface carries the supplied integral torus from the
neutral model to the full model. It uses the existing Library definitions
`IntegralTorusData`, `RelativeComponentModelData`, and `IntegralSplitTorusData`.
It supplies an input to the integral root-model construction without asserting
existence of a torus, a model, or a building.

Fix an arbitrary universe `u`, a domain `R` with fraction field `K`, an actual
group scheme `G` over `K`, supplied relative-component model data `D`, an actual
commutative group scheme `S` over `K`, a map `i : S.toGrp ⟶ G`, and supplied
`T : IntegralTorusData D S i`. The hypothesis `hT` states that the actual
integral group `T.torus.toGrp` is a split torus.

`IntegralTorusData.toFullIntegralSplitTorusData T hT` constructs
`IntegralSplitTorusData D.full i`. Its integral torus is `T.torus`, its split
property is `hT`, and its inclusion into the full model is the composite
`T.inclusion ≫ D.inclusion.hom`. The generic torus identification is precisely
`T.genericIso`, expressed in the commutative-group category by the Library's
`CommGroupScheme.isoOfGroupIso`.

The commuting generic square follows by functoriality of base change. The
square for `D.inclusion` identifies its generic map with the identity on `G`.
After cancelling this identity, the composite square becomes the supplied
`T.generic_comm`. No additional compatibility assumption is required.

`toFullIntegralSplitTorusData_inclusion` records the composite inclusion, and
`toFullIntegralSplitTorusData_integralCharacter` shows that the resulting
integral character is exactly the character from
`T.toIntegralSplitTorusData hT`, the existing neutral-model conversion. Both
are definitional equalities because the torus, splitting proof and generic
identification are retained. This conversion requires no closedness or
special-fibre maximality hypothesis and proves no such property.
