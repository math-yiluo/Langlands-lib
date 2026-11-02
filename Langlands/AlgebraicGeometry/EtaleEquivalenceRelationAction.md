# Actions of étale equivalence relations

Author: Worker 706.

This internal scheme-level construction supplies the action interface needed
for the presentation approach to Noetherian approximation. It is derived
from the existing equivalence relation and fibre product interfaces, without
assuming a quotient or a descent theorem. The motivating action, change of
charts, and pushout steps are in Stacks Project Proposition 70.8.1, Tag 07SU,
registered as `stacks-noetherian-approximation-2026-11-01`. The convention for a
cartesian morphism is Definition 39.21.1, Tag 0APD, registered as
`stacks-etale-equivalence-relations-2026-11-01`.

`EtaleEquivalenceRelation.Action E p` is an action on a scheme
`p : P → E.U`. Its `map` sends a pair consisting of an original arrow
`(x,y)` and a point of `P` over `y` to a point of `P` over `x`.
The equation `over` expresses compatibility with `p`. The field `unital`
states that the unit acts as the identity. The field `associative` states,
on every scheme-valued point, that successive actions agree with the
action of the composite, in the composition convention of
`EtaleEquivalenceRelationGeometry`.

In namespace `Action`, `act` evaluates this map on a compatible arrow
and point. `act_congr` allows equal arrow and point inputs to be substituted
while retaining their compatibility proofs. `act_over` describes its image under `p`; `act_precomp`
proves naturality in the test scheme; and `act_arrow` recovers the action
map after a morphism to its fibre product domain. `act_unit` derives
the unit law on every test scheme from `unital`. `act_assoc` is the
associative law written using `act`. `act_inverse` follows by applying
associativity to an arrow and its inverse and using the unit law.

`inverseMap` reverses an action arrow by reversing the original arrow
and using its action value as the new source point. The equations
`inverseMap_fst`, `inverseMap_snd`, and `inverseMap_map` describe its
original arrow, source, and target. `inverseMap_inverseMap` follows from
these projection equations and the involution of original arrows.
`inverseIso` packages reversal as an involutive isomorphism.
`etale_snd` follows by base change of `E.s`. `etale_map` follows by
composing that projection with the reversal isomorphism. Neither result
requires `p` to be étale.

`relation` is the resulting étale equivalence relation with object scheme
`P`, arrow scheme `E.R ×_{E.U,s,p} P`, target `map`, and source the second
projection. Its monomorphism follows by comparing both endpoints in the
original relation and then using fibre product uniqueness. The unit,
reversal, and associative action give reflexivity, symmetry, and
transitivity respectively. `isCartesianHom` proves that the maps `p`
and the first projection form a cartesian morphism to `E`, using the
defining fibre product square. `isAffine_relation` proves affineness of
the action relation's arrow scheme when `E.U`, `E.R`, and `P` are affine.
All schemes retain the arbitrary universe `u`.
