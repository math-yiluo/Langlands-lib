# Open subgroups over a field without a finite-type ambient group

Worker 596.

`DivisionStable G U` says that the image in `G` of `p * q⁻¹` lies in `U` when
both `p` and `q` have image in `U`, for all points with values in every field
in the same universe. The scheme `G` is an actual group object over a field.

`isClosed_of_divisionStable` proves that an open such `U` is closed, and
`clopen` packages it as an actual clopen subset. The ambient group has no
finite-type, quasi-compactness, separatedness or smoothness hypothesis.

## Implemented proof and provenance

This is an internal generalization of the existing
`Langlands.GroupScheme.isClosed_of_isOpen_of_mul_inv_mem` proof in
`Langlands.AlgebraicGeometry.Picard.FieldGroupOpenSubgroupClosedProof`.
The existing proof assumes that the ambient group is locally of finite type
and uses closed points over an algebraically closed field. The present proof
uses points with arbitrary residue fields instead. The finite-type condition
is thus unnecessary when division stability is known for every field.

If `U` is nonempty, division of one residue-field point by itself puts the
identity in `U`. Its image is independent of the chosen field extension.
For a point `y` in the closure of `U`, base change to `κ(y)` gives a section
`s`. The projection from this field base change is open, so `s` lies in the
closure of the preimage `U_K`. The morphism `ρ(z) = s * z⁻¹` maps `s` into
`U_K`, since it sends `s` to the identity. The open set `ρ⁻¹(U_K)` therefore
meets `U_K`. Choose any point of this intersection and evaluate at its
residue-field point; no rational-point or closed-point assertion is needed.
Division stability then puts `s` in `U`, proving that `y` belongs to `U`.

`divisionStable_range` checks the hypothesis for an actual homomorphism
whose underlying map is an open immersion: lift each field-valued point
uniquely through that immersion, divide in the source group, and use the
homomorphism laws. `isClosed_range` proves closedness of that actual image;
`clopenRange` packages it as a clopen subset.

This internal construction supplies closedness of an open subgroup of an
infinite-type affinization. It does not itself construct that affinization's
group law or prove quasi-affine field groups affine.
