# Semilinear actions on the existing apartment quotient

This is an internal algebraic construction for the published
`ApartmentQuotient P`. Its input is a group `H`, a subgroup `N` acting on an
apartment type `A`, and the original conjugation-covariant family `P` of
subgroups of `H`. It uses the original quotient relation and the existing
`H`-action by multiplication of the first coordinate.

For a group `Γ` and a homomorphism `ρ : Γ →* MulAut H`,
`SemilinearActionData P ρ` supplies an action on `A`. It requires that `ρ`
preserve `N`, that the apartment action intertwine the `N`-actions through
`ρ`, and that `ρ σ` send `P x` into the subgroup at the transformed
apartment point. These hypotheses are explicit; this module does not
construct them from valued-field or reductive-group data.

For representatives `(g,x)`, the map associated with `σ` sends the class to
the class of `(ρ σ g, D.apartment σ x)`. The quotient relation is respected:
its normalizer witness is sent through `ρ σ`, apartment equivariance
preserves its first condition, and subgroup compatibility and preservation
of multiplication and inversion preserve its second condition.

The identity and product laws follow on representatives from the two
supplied homomorphisms. The maps for `σ` and `σ⁻¹` are mutual inverses.
`SemilinearActionData.action` therefore constructs a homomorphism into
the permutations of the existing quotient, with proved formulas on
representatives and on the canonical apartment.
`action_smul` intertwines the original `H`-action through `ρ σ`;
`action_smul_eq_iff` preserves and reflects full point fixation.

The provenance is the existing apartment quotient and elementary group
action algebra. No new original-literature result is asserted. No metric,
continuity, building availability or fixed-point descent follows here.
In a Galois application, the apartment action, normalizer stability and
sharp-fixer compatibility still have to be established on the actual data.
