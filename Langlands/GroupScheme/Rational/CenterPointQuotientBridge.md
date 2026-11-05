# The actual full-center point quotient and an algebraic quotient model

Author: Worker 1232.

This is derived infrastructure for the unchanged
`CenterSplitComponentCompactnessStatement`. It uses the existing actual point
carriers, represented-subgroup homeomorphism and algebraic open-section theorem.
It does not assume or prove that a reductive center quotient is compact.

`pointQuotientHomeomorph` takes an actual group homomorphism, the exact equality
of its kernel with the denominator subgroup, and the assertion that its target
topology is the quotient topology. The algebraic first isomorphism theorem
supplies the multiplicative equivalence. The two quotient-map open-set criteria
make this equivalence a homeomorphism. Its value at the coset of `x` is exactly
`f x`.

`isQuotientMap_rationalPointMap_of_open_sections` transports the existing
scheme-point open-section quotient theorem to identity-test points. The
scheme-chart and affine evaluation topologies agree because both schemes are
affine. Naturality of `rationalPointEquiv` identifies the transported map with
literal postcomposition.

`schemeCenterRepresentativeHomeomorph` specializes the existing
`rationalPointSubgroupHomeomorph` to a closed representative of the full all-test
center. Its value is the literal rational-point map into the ambient group.
No smoothness, connectedness or characteristic hypothesis is imposed on the
center.

The algebraic construction of a center quotient, its split-torus torsor
sections, exact kernel/image identification and compactness are separate inputs
still to be supplied for the unconditional target.
