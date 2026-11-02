# The action associated to a cartesian relation morphism

Author: Worker 706.

This is an internal construction derived from the source pullback square in
`EtaleEquivalenceRelation.IsCartesianHom` and the structural maps in
`EtaleEquivalenceRelationGeometry`. It supplies the action needed when descending
a chart across a cartesian relation morphism. It assumes no approximation,
quotient, or descent statement. The source-square convention is Definition
39.21.1, Stacks Project Tag 0APD, registered as
`stacks-etale-equivalence-relations-2026-11-01`. The motivating change of
presentations occurs in Proposition 70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`.

The namespace `EtaleEquivalenceRelation.IsCartesianHom` fixes a cartesian
morphism `h` from `E` to `F`, with object map `f` and arrow map `g`.
`unit_naturality` and `compose_naturality` show that these maps preserve
the units and composition. Both proofs compare endpoints in `F` and use
the uniqueness of arrows with given endpoints.

For a lower arrow `r` and an upper point `v` whose images match at the source,
`liftArrow` is the unique upper arrow supplied by the source pullback square.
`liftArrow_g` and `liftArrow_s` recover its image and source.
`liftArrow_t_over` gives the image of its target in `F.U`.
`liftArrow_unit` follows from preservation of units and uniqueness in the
source square.

`actionMap` is the inverse of the pullback comparison isomorphism followed
by `E.t`. `actionMap_over` gives its compatibility with `f`.
`lift_actionMap` identifies its evaluation on any compatible pair with the
target of `liftArrow`. `liftArrow_comp` identifies the lift of a lower
composite with the composite of the two successive upper lifts; its proof
uses preservation of composition and uniqueness in the source square.

`action` packages this map as an action of `F` on `f : E.U → F.U`.
The unit law follows from `liftArrow_unit`. The associative law follows
from `liftArrow_comp` and the target of a composite. `action_act` records
the evaluation formula.

`actionRelationIso` is the source pullback comparison isomorphism between
`E.R` and the arrow scheme of the canonical action relation.
`actionRelationIso_t` and `actionRelationIso_s` show that it preserves
both endpoints. `isCartesianHom_action` pairs these compatibilities with
the pullback square of an isomorphism over the identity. Thus the canonical
action recovers the original relation, with its original object scheme.
Every construction retains the arbitrary scheme universe `u`.
