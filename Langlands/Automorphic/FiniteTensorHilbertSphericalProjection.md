# Canonical spherical projections on full completed tensor slices

This internally derived unit specializes the existing orthogonal joint Hecke
projection to the canonical spherical data. Its inputs remain a genuine tensor
presentation and an invariant positive form on the actual global realization.
It also relates identity of the constructed projection to the existing
whole-space scalar-spectrum relation. No new original-literature identification
is asserted.

For a family of bounded complex operators on a Hilbert space,
`jointOrthogonalProjection_eq_id_iff` proves that the actual joint orthogonal
projection is identity exactly when every operator acts on every vector by
its prescribed scalar. The forward proof evaluates equality of continuous
maps at each vector and uses the existing fixed-vector criterion. The reverse
proof uses extensionality and the same criterion.
`hasScalarSpectrum_iff_jointOrthogonalProjection` retains nontriviality as a
separate conjunct, including when the Hilbert space is zero. The group-free
result allows an arbitrary index universe independent of the carrier universe.

`cornerJointOrthogonalProjection_eq_id_iff` proves the corresponding criterion
on all subgroup-fixed vectors of a closed invariant subspace of a complete
norm-preserving representation. Its equations use the unchanged algebraic
corner action. The proof again evaluates maps and uses the existing exact
fixed-vector criterion. `hasScalarSpectrum_iff_cornerJointOrthogonalProjection`
retains nontriviality and all scalar equations; it adds no finite-dimensionality,
admissibility or commutativity requirement.

For a p-adic field with its canonical local GL topology, a complete complex
inner-product representation and a closed invariant subspace,
`sphericalJointProjection` applies the existing corner projection using exactly
`Unramified.sphericalHaar`, `sphericalOpenSubgroup`,
`standardHeckeElement` and `standardHeckeScalar`. The Haar measure has the
existing mass-one normalization on the integral subgroup. All standard
diagonal indices are present, including the endpoints. The residue-cardinality
square-root normalization of the scalar is unchanged.
`sphericalJointProjection_range` applies the existing corner range law to
identify its range with the actual ordinary joint eigenspace of those
algebraic operators. `hasScalarSpectrum_iff_sphericalJointProjection`
specializes the generic whole-spectrum criterion to this same construction.
The inherited orthogonal-projection laws remain applicable.

`sliceHilbertSphericalProjection` specializes this construction to
`sliceHilbertRange` inside the supplied global positive-form Hilbert
completion. Its ambient group action is the original completed representation
restricted along the actual local inclusion. The existing range-closedness
proof and `completedRepresentation_norm` discharge the construction inputs.
The operator acts on all spherical fixed vectors of that full closed slice,
with the inherited global norm. The generic canonical spectrum criterion applies to these same inputs,
without a separate concrete wrapper theorem.

The number field and original local-factor family have independent universes.
Coefficients are complex and the rank is every positive natural number,
written `r + 1`. The complementary tensor may be zero. Neither construction
nor the spectrum equivalence assumes factor irreducibility, admissibility or
a nonzero tail. The unit does not assert nontriviality, existence of a
prescribed spectrum, commutativity, a spectral decomposition, automorphic
occurrence, a tensor presentation or a positive form.
