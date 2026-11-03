# Fpqc locality of subgroup membership and normalization

This internal module supplies a descent step for the arbitrary-field
relative-root factorization argument. It uses only the published subgroup
functors, their all-refinement normalizers, and effective-epimorphism descent.
It does not require a represented normalizer.

`SubgroupFunctor.HasFpqcMembershipDescent F` means that, for every fpqc map
of test schemes, a point belongs to `F` whenever its restriction belongs to
`F`. The map is required to be quasi-compact, flat and surjective on
underlying schemes. This condition concerns an already given ambient
point; it asserts no surjectivity on rational points.

`hasFpqcMembershipDescent_range` establishes the property for the range of
a group-scheme homomorphism that is a monomorphism over the base. It applies
the existing `mem_range_of_comp_mem_range`: the local factorization through
the monomorphism descends by effective epimorphism.

`HasFpqcMembershipDescent.normalizer` proves that the property is preserved
by taking the existing all-refinement normalizer. For each refinement of
the original test scheme, the proof pulls back the cover. Local
normalization sends the restricted subgroup point and its two conjugates
back into the subgroup; the membership-descent hypothesis then descends
both conjugate memberships.

`mem_torusNormalizer_of_comp_mem` specializes this to the actual image of
a monomorphic torus map. In particular, normalization of a given rational
point may be verified over an fpqc cover without assuming that the torus
has a rational inversion point.
