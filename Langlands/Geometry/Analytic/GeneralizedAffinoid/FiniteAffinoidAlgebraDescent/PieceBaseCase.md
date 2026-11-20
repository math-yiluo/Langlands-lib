# Matching families over a full domain inside one cover member

This helper module works in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent`.
Fix a complete ultrametric normed field `K`, a presented affinoid algebra `R`, a
finite full-domain cover `c` of the whole spectrum of `R`, and local algebras
`F : LocalAlgebras c`. Its results are internal derivations from the
definitions of `LocalData`, `EffectiveData` and `PieceMatching`. They cite no
outside literature.

## Restricted transitions

In the namespace `PairTransitions`, for pair transitions `t`:

- `restrict_transition_assoc`: the published `restrict_transition` (restricted
  transitions commute with restriction), composed on the right with an
  arbitrary bounded map.
- `transition_self_of_identity`: if the transition `t.equiv i i` on the overlap
  `cᵢ ∩ cᵢ` is the identity, then so is its restriction `t.transition i i E`
  to every full domain `E ⊆ cᵢ`. Both maps agree on the two legs of the
  affinoid pushout, so `AffinoidPushout.hom_ext` applies.
- `transition_cocycle_of_triple`: the cocycle identity on the triple
  intersection `cᵢ ∩ cⱼ ∩ cₖ`, stated for the restricted transitions on that
  intersection, implies the same identity on every full domain `E` contained
  in `cᵢ`, `cⱼ` and `cₖ`. Again the two sides are compared on the pushout legs.
  The local leg factors through the restriction from the triple intersection,
  and the base leg is preserved by every transition.

`inter_subset_of_subset`: if `U ⊆ cᵢ₀`, then `U ∩ cⱼ ⊆ U ∩ cᵢ₀`.

## Matching families from one piece

In the namespace `DescentData`, for descent data `d` (pair transitions with
the identity and cocycle conditions):

- `restrict_transition_apply`: elementwise form of `restrict_transition`.
- `ofPiece i₀ hU x`: for a full domain `U ⊆ cᵢ₀` and an element `x` of the
  piece `F.baseChange i₀ (U ∩ cᵢ₀)`, the family whose `j`-th component is the
  restricted transition from `i₀` to `j` on `U ∩ cⱼ`, applied to the
  restriction of `x`. The matching condition on a full domain `E ⊆ U ∩ cⱼ`,
  `E ⊆ U ∩ cₖ` follows from `transition_cocycle_of_triple` for `(i₀, j, k)` on
  `E`, after both components are rewritten as transitions from `i₀` on `E`.
- `ofPiece_apply`: the defining formula for the components (by `rfl`).
