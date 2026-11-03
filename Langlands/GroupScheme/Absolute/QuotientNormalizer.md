# Rational normalizers under exact quotient preimages

Author: Worker 1369.

This internal construction works over an algebraically closed field
`k : Type u` for arbitrary universe `u`. The actual group-scheme
homomorphism `q : G → Q` is assumed surjective and locally of finite type
as a morphism of schemes. No smoothness, connectedness, affineness or
centrality assumption is needed for this unit.

`exists_rationalPointLift` applies the published
`Langlands.exists_point_lift_of_locallyOfFiniteType_surjective` to an
actual `k`-point of `Q`. The resulting scheme map to `G` is a morphism
over `Spec k`: its composite with the structure map equals the identity
by the lifting equation and the two over-category triangles.
`rationalPointLift` chooses this lift. The equality
`rationalPointLift_comp` identifies its composite with `q` with the
original point, and `rationalPoints_surjective` states surjectivity of
the actual induced group homomorphism on base points. These assertions
concern algebraically closed base points.

For a subgroup functor `F` of `Q`,
`SubgroupFunctor.normalizer_carrier_base_comap_eq` says that the abstract
normalizer of the base points of `F.comap q` equals the group-theoretic
preimage of the abstract normalizer of the base points of `F`. The proof
uses the existing Mathlib theorem
`Subgroup.comap_normalizer_eq_of_surjective` and the just-established
surjectivity on base points. The existing definition of subgroup-functor
`comap` is pointwise group-theoretic preimage, so no additional comparison
or representability assumption is required.

`SubgroupFunctor.normalizer_carrier_base_eq_of_quotient` takes an exact
all-test equality `FQ.comap q = F` and rational self-normalization of
`FQ`, then proves rational self-normalization of `F`. It rewrites by
the preimage equality and the preceding normalizer identity, and uses
the supplied quotient normalizer equality.

The intended use is the central quotient branch of dimension induction
for the exact Borel normalizer theorem. The geometric construction of
the central quotient, descent of the Borel with its exact inverse
image, and self-normalization of the smaller quotient's Borel are
retained consumer obligations. This unit proves none of those structural
inputs and assumes no global Borel normalizer or parabolic normalizer
statement. Its provenance is the published algebraically closed
point-lifting theorem, the existing all-test preimage definition, and
Mathlib's group normalizer theorem.
