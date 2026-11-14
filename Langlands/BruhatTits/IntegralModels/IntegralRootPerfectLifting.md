# Integral root lifts over a perfect residue field

This internal supporting unit extends the earlier integral root lift and
higher-multiple witness from an algebraically closed residue field to a perfect
residue field. The integral base remains a Henselian local domain with the
specified fraction field. The smooth neutral component model, integral split
torus, actual generic torus identification, and actual reductive special-fibre
quotient remain unchanged. Everything has arbitrary universe `u`.

For any nonzero generic character and any prescribed point of its specialized
intrinsic quotient-root subgroup, the perfect-field smooth-root lifting theorem
gives an actual point of the corresponding special-fibre root subgroup above it.
The integral split root model represents that root subgroup. Smooth Henselian
reduction lifts the resulting point to an integral root-model section. Its image
in the neutral model has the specified exact quotient reduction and its generic
point belongs to the original intrinsic root subgroup.

`perfectResidueRootQuotientLift` chooses such a section; its accompanying
specification theorem retains generic root membership and exact quotient image.
The proof uses the canonical integral character transported through the actual
generic and special torus identifications, as in `IntegralRootQuotientLifting`.

If the specialized character is an actual quotient root, the arbitrary-field
rational witness of `RootPointOutsideCyclicTail` supplies a quotient-root point
outside the root subgroup of any prescribed natural multiple `n` with `2 ≤ n`.
The preceding integral lift preserves that exclusion in actual quotient
reduction. If the generic point belonged to the higher-multiple root group,
the all-test integral root reduction theorem would put its quotient reduction
in that same higher-multiple subgroup, a contradiction.

`perfectResidueIntegralRootPointOutsideMultiple` chooses an actual integral
section with generic root membership, membership in the actual quotient-root
group, and exclusion from the higher-multiple group both generically and in
quotient reduction. Perfection is used only for rational root-map lifting;
the root witness itself works over every field. The construction composes the
named Library and separately submitted internal results, without a new external
source assertion. It supplies no facet-depth vanishing or final derivative
root-datum proof.
