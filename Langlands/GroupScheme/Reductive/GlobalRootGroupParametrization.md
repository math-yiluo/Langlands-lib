# Global torus-equivariant root parametrizations

This internal construction completes the global coordinate construction by identifying
the coordinate's full torus weight from its fixed field-fibre weights.
It uses idempotent weight-projection coefficients to retain nilpotents in the
arbitrary base. No new external source assertion is used.

Scalar multiplication of a coordinate evaluates through the coefficient
algebra. Suppose a nonzero scalar multiple of the coordinate is homogeneous
of exponent m. On every field test where that scalar remains nonzero, the
prescribed equivariant fibre and the polynomial coordinate identify the
torus action on the coordinate with exponent a. Comparing the homogeneous
scalar multiple and cancelling that scalar gives equality of the two
character values on those tests.

Each full-torus weight projection of the coordinate remains in its
one-dimensional coordinate degree, so it is a scalar multiple r_m of the
coordinate. Idempotency of the projection and faithfulness of the free line
make r_m an idempotent scalar. If r_m survives modulo a maximal ideal, use the
fraction field of the exponent group algebra over that residue field.
The universal monomials are independent there, so the character-value
comparison forces m = a. Thus every wrong r_m belongs to every maximal ideal.
It lies in the Jacobson radical, which makes 1-r_m a unit; idempotency forces
r_m = 0. Summing the weight projections now proves that the original
coordinate is homogeneous of the prescribed full-torus weight.

This argument retains nilpotent elements of the arbitrary base ring: the
scalars eliminated after passing to residue fields are idempotents, and the
Jacobson argument proves their actual vanishing in the base ring.

`exists_isRootParametrization_of_free_weight_of_fibres` combines that
homogeneity with the previously constructed global polynomial coordinate.
Positive-degree additivity gives an actual additive-group isomorphism onto
the dynamic root group, followed by its actual closed inclusion. The
all-test weight formula proves torus equivariance and the published
representation comparison identifies the actual root subgroup.

`rootParametrizationOfFreeWeightOfFibres` chooses the actual map, and
`isRootParametrization_rootParametrizationOfFreeWeightOfFibres` proves the
representation, closed-subgroup and all-test equivariance properties of
that chosen map.

The supplied-data assumptions are an affine smooth ambient group, a root
character with zero centralizing pairing and positive integral contracting
pairing, an explicit free actual root-weight trivialization, and fixed
torus-equivariant additive-group fibres. The base is any commutative ring in
universe u, including the zero ring; it need not be connected, reduced,
local or a field. Deriving the fibre data from reductivity and the root datum
is a separate specialization step, carried out in
`GlobalSplitRootParametrization`.
