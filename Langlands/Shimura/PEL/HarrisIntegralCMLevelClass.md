# Raw fixed Weil levels and normalized integral CM representatives

This module is an internal composition of the actual integral full-action
condition, canonical polarization pullback, the fixed Weil-level orbit tower
and the existing normalized integral CM class quotient.

Fix the universe-zero arithmetic data, normalized charts, prerequisite package,
an ambient polarized abelian family with its selected dual witness, and an
actual full-order action on a direct test pullback. The action satisfies the
existing full-order Rosati and normalized determinant condition. The test has
the existing pointed finite-fibre, torsion-unit, finite root-of-unity and
quasi-separated inputs of the actual Weil level tower.

`harrisIntegralCMFullActionLevelTower` constructs the actual tower of
monodromy-fixed right orbits of Weil-compatible frames for the direct family,
rational extension of the integral action and canonical pullback polarization.
The index functor is the original `hodgeLevelFunctor`, retaining the original
Harris transporter convention. It needs no supplied faithful polarized action.

Every member of this tower has a frame representative. The
`_nonemptyFrame` theorem forgets its pairing structure to obtain mere existence
of an actual Harris frame. No representative is asserted to be fixed by
monodromy. `harrisIntegralCMFullActionLevelData` uses this existence to derive
faithfulness through the published polarized-action constructor, and retains
the same orbit. Thus no separate frame-existence premise is required.

With the ambient prescribed relative dimension,
`harrisIntegralCMFullActionLevelRepresentative` constructs the existing
`IntegralCMRepresentative`. Its actual integral restriction is the original
action; its determinant and dimension are the unchanged normalized condition
proved by the polarized-action construction. The relative dimension assumption
remains explicit.

The transporter theorem identifies this representative after every original
Harris level map with the existing representative map. The final natural
transformation sends the lifted raw level tower to the existing integral CM
class tower. Both maps retain the same rational-isogeny quotient; proof
irrelevance identifies the faithfulness proofs extracted from the two orbits.

This construction does not assert existence of a fixed level orbit or a
representing level scheme, ambient moduli representability, admissibility,
smoothness or division projectivity. It does not yet prove naturality in base
morphisms or geometric-point changes. Those are separate obligations of the
host representability proof.
