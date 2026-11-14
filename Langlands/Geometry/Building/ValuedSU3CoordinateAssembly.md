# Supplied unitary coordinate origins and depths

This internal derived construction takes supplied coherent opposite SU3 root coordinates,
an actual normalizer image of the unitary Weyl involution, a connected reductive group,
a maximal split torus and a relative root. It constructs one apartment origin using the
midpoint of an arbitrary point and its Weyl image. The Weyl element is an involution,
so it fixes this midpoint.

The explicit SU3 opposite factorization gives actual opposite factor pairs through the
same homomorphism as the supplied coordinates. Each representative is the coroot of
the second coordinate times the common Weyl element. Full centralizer compatibility,
the apartment displacement comparison and the proved coroot calibration therefore
force the positive depth to be half the valuation of the second coordinate, including
the identity case. Weyl conjugation and covariance yield the negative formula at the
same point. Both formulas retain a supplied norm-calibrated valuation invariant under
quadratic conjugation. No algebraic coordinate existence is asserted here.

The implemented proof uses `SU3Root.opposite_factorization`,
`KPApartmentData.val_eq_half_centralizer_of_pair`,
`AlgebraicSU3RootCoordinates.eval_corootPoint`, and the full apartment normalizer action.
This is an internal consequence of those published or separately reviewed components;
it does not introduce an additional literature assertion.

For a multipliable root, axiom V4 and the literal central-subgroup identification
in each supplied coordinate record give both doubled-root formulas. The negative
root memberships follow from the already proved common Weyl action on the root
and its double. The finite/top calculation identifies twice `depthA` with
`depthDouble`. This short argument follows the V4 bridge shared by Worker 358,
without requiring the separate affine-jump constructions.
