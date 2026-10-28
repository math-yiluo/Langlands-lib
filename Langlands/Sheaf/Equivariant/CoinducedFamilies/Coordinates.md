# Coordinates for coinduction of arbitrary stalk families

Author: Worker 865.

This module computes sections of the actual published `coinduction` applied to
the ordinary sheaf underlying `Godement.zeroSheaf F.obj`. It is an internal,
derived construction from the published transport category, degree-zero
Godement sheaf, coinduction, and Mathlib's pointwise right Kan extension API.
It does not introduce a separate model of coinduction or assume a comparison.

All types have an arbitrary common universe `u`. The assumptions are a
commutative ring `R`, a group `G`, a topological space `X`, a `G` action on `X`
whose individual translations are continuous, and an equivariant
`ModuleCat R`-valued topological sheaf `F`. No topology on `G`, smoothness,
local compactness, or separation assumption on `X` is needed here.

`Coefficients F y` is the stalk at `y` of the ordinary sheaf underlying `F`.
For an object `U` of the transport category, `Sections F U` is the module

```text
∀ (g : G) (y : {y : X // g • y ∈ U.openSet}), Coefficients F y.1.
```

`ordinaryZero F` is the ordinary sheaf underlying `Godement.zeroSheaf F.obj`.
`coinducedZero F` is exactly `(coinduction G X (ModuleCat R)).obj
(ordinaryZero F)`. The selected definition `read F U` is a linear equivalence
from its sections over `U` to `Sections F U`. It comes from the module
isomorphism `coordinateIso F U`.

The main compatibility is `read_map`: for `f : U ⟶ V`, a section `s` over `V`,
a group element `g`, and `y` with `g • y ∈ U.openSet`,

```text
read F U (coinducedZero.map f.op s) g y
  = read F V s (f.label * g) y.
```

The right-hand membership follows from `f.mapsTo` and the action law. Thus an
ordinary restriction (whose label is one) drops coordinates outside the smaller
open; a labelled transport multiplies the group index on the left and preserves
the coefficient's stalk point. The formal expressions retain all membership
proofs in the subtype indices.

The implementation computes the pointwise limit defining the right Kan
extension. `coordinateOpen U g` is the full inverse translate
`{y | g • y ∈ U.openSet}` and `coordinateArrow U g` maps it to `U` with label
`g`. For an object `d` of the structured-arrow category at `op U`,
`familyComponent` evaluates a family at `d.hom.unop.label` on the source open.
This gives `familyCone`; its naturality uses the group-label equality of a
structured-arrow morphism and `Godement.stalkPull_one_section` for ordinary
restrictions.

`familyConeLift` reconstructs a family from any cone by evaluating each
component on the full inverse translate. `coordinateFactor` restricts that full
translate to any smaller source open with the same label. Cone naturality for
this factor and identity stalk transport prove the factorization property.
Evaluation on the full translates proves uniqueness. These facts establish
`familyConeIsLimit` without computing Mathlib's chosen limits.

The underlying presheaf of `coinducedZero F` is definitionally the right Kan
extension along `(ActionOpens.inclusion G X).op`. Mathlib's
`isPointwiseRightKanExtensionRanCounit` and uniqueness of limit cones therefore
give `coordinateIso`, hence `read`. The compatibility of that isomorphism with
each cone projection proves `read_arrow`, an evaluation formula on any ordinary
source open carrying a labelled arrow to `U`. Applying `read_arrow` first to
`coordinateArrow U g` and then to its composite with `f`, and using functoriality,
proves `read_map`.

This module supplies coordinates and transport for later compact cutoff
arguments. It makes no compact-support or c-softness assertion by itself.
