# Algebra equivalences on algebraic-space ring points

`Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints.changeRingEquiv X e`
identifies the actual points of an algebraic space `X` over a commutative ring
`C` after a `C`-algebra equivalence `e : A ≃ₐ[C] B`. Its forward map is
`changeRing e.toAlgHom`, and its inverse is `changeRing e.symm.toAlgHom`.
The two inverse laws follow from coefficient-change composition and identity.

The definition and its `changeRingEquiv_apply` and `changeRingEquiv_symm_apply`
simp lemmas are moved unchanged from `Global.AdelicSpaceWeilRestrictionPoints`.
The explicit `X` argument, universe, public names and inverse computation are
preserved. Both the adelic Weil-restriction and full-preimage constructions
reuse this single equivalence. This is a reorganization of published content.
