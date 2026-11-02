# Cartesian morphisms of action relations

Author: Worker 706.

This internal construction combines the universal properties of action-arrow
fibre products with the source square of a cartesian relation morphism.
It assumes no approximation or quotient result. Its intended application is
the descent of charts with actions in Stacks Project Proposition 70.8.1,
Tag 07SU, registered as `stacks-noetherian-approximation-2026-11-01`.
The source-square convention is Definition 39.21.1, Tag 0APD, registered as
`stacks-etale-equivalence-relations-2026-11-01`.

Fix a cartesian morphism `h` from relations `E` to `F`, with object map `f`
and arrow map `g`. Let `p : P → E.U`, `q : Q → F.U`, and `k : P → Q`
satisfy `p ≫ f = k ≫ q`. In namespace
`EtaleEquivalenceRelation.Action`, `arrowMap` sends the pair `(r,v)` to
`(g(r),k(v))`. The equations `arrowMap_fst` and `arrowMap_snd` recover
these components.

For actions `A` and `B` on `p` and `q`, `IsEquivariant` asserts the single
morphism equality `A.map ≫ k = arrowMap ≫ B.map`.
The theorem `isPullback_arrowMap_snd` proves that the action-arrow map and
`k` form a pullback square with the source projections. It requires no
pullback hypothesis on the square containing `p,q,k,f`.
For uniqueness, the original source pullback determines the original arrow,
and the action-arrow fibre product determines the pair. For existence, a
lower action arrow and its prescribed upper source point give an upper
original arrow through the original source square; pairing it with that
point gives the required action arrow.

`isCartesianHom_of_isEquivariant` adds target compatibility from
equivariance to this source square, obtaining a cartesian morphism between
the induced action relations. `act_naturality` precomposes equivariance
with a compatible pair from any test scheme. Its pullback components show
that this is exactly the equation comparing evaluation before and after
`k`. All schemes and test schemes retain arbitrary universe `u`.
