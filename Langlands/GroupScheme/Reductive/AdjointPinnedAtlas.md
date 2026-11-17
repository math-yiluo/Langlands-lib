# Adjoint pinned charts with nontrivial geometric fibres

Worker 632.

This internal construction applies the proved étale local splitting
theorem to the exact hypotheses of the affine adjoint Weil-restriction
problem. The motivating source is Brian Conrad, *Reductive group
schemes* (2014), the proof of Proposition 6.4.4 and Remark 6.4.5,
pp.232–233, registered as `conrad-2014-reductive-group-schemes`.

`AffineAdjointPinnedChart G` consists of an `AffineAdjointPinnedModel`
identified with the actual pullback of `G` along an étale morphism,
together with nontriviality of every geometric fibre of that model.
Thus the full coordinate root datum has integral root span equal to the
whole character lattice. This is supplied data, with no weakening to a
saturated or rational span.

The existence proof starts with the affine pinned chart supplied by the
Library's proved local splitting theorem. Adjointness and nontriviality of
the geometric fibres pull back to this chart. Its distinguished point
then proves the constant integral root-span condition using
`AffinePinnedModel.isAdjoint_geometricFiber_iff`. The original chart
isomorphism transfers the nontrivial-fibre condition to the pinned model.

`AffineAdjointPinnedAtlas.ofReductive` chooses such a chart over every
point. It provides the actual étale covering family and the surjective
étale morphism from the disjoint union of the charts. Forgetting the
additional conditions recovers an ordinary affine pinned atlas. No finite
subcover or quasi-compactness assumption is imposed. The empty base is
allowed; the point-indexed family is then empty.

When the original base is `Spec A`, `chartAlgebra` equips each chart ring
with precisely the algebra structure obtained from its original spectrum
map. `algebraBaseMap_chart` verifies that this algebra structure retains
that map. All rings, schemes and chart indices lie in the arbitrary
universe `u`. This module supplies local charts and their comparisons; it
does not construct the simple factors or carry out descent of a Weil pair.
