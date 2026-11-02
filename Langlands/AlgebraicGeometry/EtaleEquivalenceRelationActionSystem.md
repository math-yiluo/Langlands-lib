# Eventual actions in cartesian relation diagrams

Author: Worker 706.

This module is an internal derived interface for action descent in the
Noetherian approximation program motivated by Stacks Project Proposition
70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`. Its mathematics is derived
from the supplied cartesian squares and object limit, ActionLimits,
ActionDomains and ActionDescent. It assumes a prospective map compatible
with the actual action; factorization of that map and existence of the
approximation system remain separate obligations. All schemes, index
objects and index morphisms retain arbitrary universe `u`.

The declarations are in `EtaleEquivalenceRelation.Action.CartesianSystem`.
Let `D` be a diagram of étale equivalence relations with cartesian
morphisms, let `t` compare `D` to a fixed relation `F`, and let `c` be a
cone with a cartesian map `m : c.pt → F`. The hypothesis `hm` states that
every cone leg followed by its designated comparison is `m`.
`objectComparison` takes the object component of `t`; its naturality
follows from naturality of `t` by taking the object component of the
cartesian morphisms. `object_cone_comparison` similarly takes the object
component of `hm`.

Suppose `q : Q → F.U` is fixed and a supplied square identifies an upper
object `p : P → c.pt.U` with its pullback, with comparison `k : P → Q`.
`objectDiagram` is the diagram of `D_i.U ×[F.U] Q`.
Its affine instance uses affineness of `F.U`, `Q` and all `D_i.U`.
`objectMap` and `pointComparison` are its varying and fixed projections.
`object_isPullback` is the defining pullback square, with the projections
ordered to agree with the action descent interface.

`objectCone` is the cone based at the actual scheme `P`, constructed by
`TargetLimit.coneOfPullback` from the supplied object square.
`objectCone_π_object` and `objectCone_π_point` give its projection equations.
`objectCone_isPullback` identifies each upper-to-level object square as a
pullback. Its proof cancels the known right pullback square from the
original supplied square, using those two projection equations.

`composableCone` is the target base change of the object diagram by
`outerArrow F q ≫ F.t`. Its point is the actual upper composable-input
domain. This uses the cartesian domain theorem
`isPullback_composableMap_target` and the same supplied object cone.
Neither construction assumes an action law or an action map on a level.

`exists_action_of_compatible_map` assumes that the object cone is limiting,
that the index category is cofiltered, that `F.U`, `Q`, the fixed
composable domain and all level object schemes are affine, and that `q`
is locally of finite type. Given an actual action `A` on `P`, a prospective
map `b : F.R ×[F.U] Q → Q` with its target equation, and compatibility
`A.map ≫ k = arrowMap m.isCartesian … ≫ b`, it constructs an action on
one pulled-back object at an index mapping to any prescribed index.
The resulting action map has the required compatibility with `b`.

The implemented proof constructs the object and composable-domain diagrams
and their actual cones explicitly. Target base change preserves the
supplied cofiltered object limit. Affineness gives quasi-compact terms and
affine transition maps. Naturality of the unit and associativity
expressions converts the two laws for `A` into equalities after the limit
legs. The existing `exists_action_at_level` descends both equalities to a
common index. At each level the identification of its actual composable
domain with the target base change is the flipped pullback isomorphism
from ActionDomains; its second projection is exactly the required
composable comparison. Thus the theorem supplies the hypotheses of
eventual law descent from actual scheme constructions.

`exists_equivariant_action_of_compatible_map` strengthens this conclusion
to equivariance between `A` and the resulting action under the actual
object cone leg and cartesian relation cone leg. Its proof checks equality
of maps to the level object using the two projections of its defining
pullback. After the fixed projection, compatibility with `b` and the
cone comparison `hm` identify the composite arrow maps. After the varying
projection, the target equations of both actions and the target square
of the relation cone leg give the equality. This proves the claimed
connection with the original action without any surjectivity assumption.
