# Extending subgroup factorizations across a dense base change

This internal construction is used on the valuative-lifting route for Task
7782. Let `j : Q ⟶ L` be a group homomorphism whose underlying scheme map
is a quasi-compact monomorphism locally of finite type. Let `b : B ⟶ L`
be another homomorphism over the same reduced scheme `S`. Suppose `B` is
integral with normal stalks, and smooth with geometrically connected fibres
over `S`. No affineness assumption on `Q` is required.

A *dense lift* in this module consists of an integral scheme `Z` over `S`,
a quasi-compact dominant morphism `z : Z ⟶ B`, and a scheme morphism
`l : Z ⟶ Q` with `l ≫ j = z ≫ b`. It must also contain the unit on a dense
test: for a dominant `s : S₀ ⟶ S`, there is a morphism `a₀ : S₀ ⟶ Z`
over `S` whose composite with `z` is the restriction of the unit of `B`.
In the intended application `Z` is the generic fibre of `B` over an
integral valuation base, and `a₀` is the generic unit.

## The proof

1. `exists_openUnitFactor_of_denseLift` maps `Z` to `P = Q ×_L B` using
   `l` and `z`. The projection `P ⟶ B` inherits monicity, local finite
   type and quasi-compactness from `j`. The map from `Z` is quasi-compact
   because its composite to `B` is quasi-compact and `P ⟶ B` is separated.
2. `integralDominantImageOpen` identifies the integral schematic image
   of `Z` in `P` with an open `V ⊆ B` by the normal-target form of
   Zariski's Main Theorem, and `integralDominantImageOpenLift` lifts
   `V` to `P`. In `P`, the restriction of the unit along `s` agrees with
   the lift of `a₀` since they agree after the monomorphism `P ⟶ B`.
   `range_comp_subset_integralDominantImageOpen` uses reducedness and
   dominance to put the full unit section in `V`. Projecting to `Q`
   gives a lift of `b` on `V`.
3. `exists_groupFactor_of_open` is independent of the geometric closure
   step. Multiplication defines a smooth surjection `V ×ₛ V ⟶ B` by the
   Library's `ReducedBaseSmooth` product lemmas: the open contains the
   unit, the fibres are smooth and connected, and the product map is
   the restriction of a group shear followed by a projection. The two
   lifts to `Q`, multiplied in `Q`, give a lift on this fppf cover.
   Monomorphic fppf factorization descent gives a scheme map `B ⟶ Q`;
   its unit and multiplication laws follow by cancellation through `j`.

`exists_groupFactor_of_denseLift` combines these steps.
`groupFactorOfDenseLift` chooses the group homomorphism together with the
equation that its composite with `j` equals `b`. The module does not prove
that a supplied torus satisfies the geometric or dense-lift hypotheses,
or assert the valuation-ring conjugacy conclusion itself.
