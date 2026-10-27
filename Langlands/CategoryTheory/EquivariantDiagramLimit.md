# Continuous limit actions for varying profinite groups

Author: Worker 13. This is an internal construction for the continuous
inverse-limit actions needed by level towers. It combines the published
`EquivariantDiagram` with Mathlib's actual profinite group and topological
space limits. It does not assume a limit action as input.

Let `J : Type v` be a small category and
`D : J ⥤ ProfiniteGrp.{max u v}` a diagram of profinite groups. The source
diagram `F` is an `EquivariantDiagram` of topological spaces in universe
`max u v w`, over the underlying group diagram of `D`. In particular,
each transition `F_i → F_j` is equivariant along the actual continuous
group homomorphism `D_i → D_j`. All three universe parameters are retained.

The acting group is Mathlib's `ProfiniteGrp.limit D`. Its elements are
compatible families `g_j ∈ D_j`; it has the group structure and topology
inherited from the product, and Mathlib supplies its profinite structure
and universal limit cone. The space is the point of
`TopCat.limitCone F.obj`. Its elements are families `x_j ∈ F_j` with
`F(f)(x_i) = x_j` for every index arrow `f : i → j`. Its topology is the
actual product-subtype topology. Mathlib's `TopCat.limitConeIsLimit`
already proves the universal property of this same cone.

`profiniteLimitTranslate D F g` is the continuous map sending a compatible
family `x` to the family whose `j`th coordinate is `F.ρ j g_j (x_j)`.
The transition-equivariance field of `F`, together with the compatibility
of `g` and `x`, proves that the resulting family remains compatible.
Continuity of each slice follows from the continuous component
endomorphisms and the coordinate projections.

`profiniteLimitUnderlyingAction` packages these maps as an actual
`Action TopCat (ProfiniteGrp.limit D)`. Its identity and multiplication
laws follow coordinatewise from the original monoid homomorphisms
`F.ρ j`. The multiplication convention is the existing left-action
convention: the product `gh` acts by first applying `h`, then `g`.

For each `j`, suppose the existing component action `F.action j` is
jointly continuous for the profinite topology of `D_j`.
`profiniteLimitUnderlyingAction_isContinuous` proves joint continuity of
the constructed limit action. For each coordinate, the map on the product
of limits is the jointly continuous component action composed with
the pair of continuous projections `(g,x) ↦ (g_j,x_j)`.
The product and subtype continuity criteria then give continuity into
the actual compatible-family space. Thus the proof uses joint
continuity of the component actions, beyond continuity of each fixed
endomorphism.

`profiniteLimitAction` stores this proved result in Mathlib's
`ContAction`. `profiniteLimitProjection` constructs an equivariant
continuous map from that action to the component action restricted
along the actual continuous homomorphism
`(ProfiniteGrp.limitCone D).π.app j`. Its underlying map evaluates at
the `j`th coordinate, as stated by `profiniteLimitProjection_apply`.

For a morphism `f : F ⟶ E` of varying-group diagrams,
`profiniteLimitMap` applies `f_j` to the `j`th coordinate.
Naturality of `f` proves compatibility of the resulting family;
continuity follows from the component maps. The component equivariance
of `f` proves equivariance for the group-limit action.
`profiniteLimitMap_apply` records this coordinate formula.

`componentwiseContinuous D` is the usual `ObjectProperty` saying that
every component action is jointly continuous. Its full subcategory
retains exactly the existing `EquivariantDiagram` morphisms between
those objects. `profiniteLimitFunctor` sends this category to
`ContAction TopCat (ProfiniteGrp.limit D)` using the constructed limit
actions and maps. Its identity and composition laws are proved by
coordinate extensionality.

The local topology instance on each forgotten group is exactly the
topology of `D.obj j`; it does not select a new topology. The shared
identity `HasForget₂ TopCat TopCat` helper is also installed locally.

The provenance is this explicit composition of the published
`EquivariantDiagram` implementation and Mathlib's
`Topology.Algebra.Category.ProfiniteGrp.Basic`,
`Topology.Category.TopCat.Limits.Basic`, continuous-action and
product/subtype topology constructions. No additional literature claim
or geometric comparison is invoked. Empty index categories and empty
compatible-space limits are permitted. The unit does not specialize to
Shimura schemes, identify a geometric deck group, construct a torsor, or
assert cofinality, surjectivity or an isomorphism from an original level
group to the group limit.
