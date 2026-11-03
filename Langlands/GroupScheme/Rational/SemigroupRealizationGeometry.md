# Geometric realization of the generated semigroup subgroup

For a smooth affine group over any field in universe `u`, an actual split-torus
automorphic action and any additive character semigroup, this internal unit
identifies the original all-test generated semigroup functor with the range of
the actual connected coordinate subgroup. Empty semigroups and semigroups
containing zero are included.

The exact tangent image of the coordinate quotient is the full span of the
ambient character weight spaces indexed by the semigroup. Passing to the
identity component preserves this image. The connected coordinate range is
smooth, connected, closed and stable under the original action; its exact Lie
image therefore makes it an admissible generator of the original semigroup
functor. Conversely, every admissible generator factors through this connected
coordinate subgroup by the imported augmentation-support calculation. These
two all-test containments prove
`range_connectedWeightHom_eq_semigroupSubgroup`.

`semigroupRepresentative` packages the constructed connected coordinate
group and its inclusion with a proof that it represents the original generated
functor. The representative uses a chosen finite split-torus identification.
The geometric consequences use only the proposition that the acting torus is
split: `isSmoothConnectedClosed_semigroupSubgroup` and
`hasLieImage_semigroupSubgroup` establish smooth connected closed realization
and the exact Lie image. Stability was already proved by the generated
functor's universal property.

`semigroupSubgroup_maximality` applies the existing Lie-image support comparison
to obtain the equivalence between the admissible support bound and containment
for any smooth connected stable closed subgroup. For
`eq_semigroupSubgroup_of_exact_lieImage`, that support bound first gives an
actual inclusion; the published full-Lie closed-subgroup theorem then gives
equality. No realization or full-Lie theorem is assumed as an extra premise.

The provenance is internal composition of the imported actual coordinate
subgroup, tangent computation, generator factorization and represented
Lie-image uniqueness results. This unit does not prove unipotence, a finite
Ga-series, or the full `SemigroupRealizationStatement`; those structural
conclusions remain separate obligations.
