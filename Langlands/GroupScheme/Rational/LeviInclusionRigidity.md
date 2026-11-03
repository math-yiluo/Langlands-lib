# Rigidity of nested rational Levi subgroups

This internal construction proves that two rational Levi subgroup maps
`l : L ⟶ P` and `m : M ⟶ P` of the same group scheme over any field have equal
images on every test scheme if `range l ≤ range m`. It constructs an actual
group-scheme isomorphism `IsRationalLeviSubgroup.isoOfRangeLe : L ≅ M`,
compatible with both inclusions, and proves uniqueness of its forward map
from that compatibility.

## Multiplication-coordinate proof

The preliminary `range_eq_of_nested_multiplication` works over any base scheme.
It assumes actual isomorphisms `subgroupMultiplication l r` and
`subgroupMultiplication m s`, together with `range l ≤ range m` and
`range r ≤ range s`. It requires neither normality nor a radical predicate.

For a point `x = y ≫ m`, the inverse first multiplication map gives coordinates
`a` and `n` with `(a ≫ l) * (n ≫ r) = x`. The two containments provide points
`z` and `w` with `z ≫ m = a ≫ l` and `w ≫ s = n ≫ r` on the same test scheme.
Applying the second Levi coordinate to
`(z ≫ m) * (w ≫ s) = y ≫ m` gives `z = y`. Hence `a ≫ l = x`,
which proves the reverse image containment. No extension of the test scheme
or restriction to field-valued points occurs.

For `IsRationalLeviSubgroup.range_eq_of_le`, the two rational Levi predicates
supply the multiplication isomorphisms and represented geometric unipotent
radicals. The ground-field greatest-subgroup properties imply equality of the
two radical images by the published `IsUnipotentRadical.range_eq`.
The preliminary lemma then applies.

## Actual isomorphism

Closedness makes each Levi map a monomorphism representing its image. The
proved image equality therefore lets the published
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` construct `L ≅ M`.
The forward and inverse comparison maps compose with the respective subgroup
maps to give the original subgroup maps. Monicity of `m` proves uniqueness of
the forward map with this property.

## Provenance and scope

This is an internal consequence of the existing actual Levi multiplication
isomorphism, its coordinate lemmas in `Rational.LeviRetraction`, and uniqueness
of represented radicals and subgroup functors. No additional structural
theorem is assumed, and no external source is needed for this derivation.

The result compares nested Levis of one specified group. It neither constructs
a Levi nor proves conjugacy of arbitrary Levis. In particular it does not
construct a compatible parabolic refinement or prove the ambient maximal split
centralizer theorem for minimal parabolics.
