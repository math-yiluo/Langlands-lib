# Maximal abelian reduction of finite Galois norm images

This derived supporting unit works in an arbitrary common field universe. It defines `maximalAbelianNormSubfield K M` as the fixed field of the commutator subgroup of the actual Galois group. For a finite Galois extension this field is abelian over the base: Mathlib identifies its automorphism group with the abelianization.

For a p-adic base field, the actual determinant-norm image from this subfield equals the norm image from the whole finite Galois extension. Norm transitivity gives containment. The finite norm equivalence from `NormExistenceFiniteSupport` identifies the whole extension's norm index with the cardinality of the Galois abelianization. The same cardinality is the degree of the commutator fixed field, and the abelian norm index is that degree. Strict decrease of finite subgroup index under strict enlargement then proves equality.

`normSubgroup_le_of_tower` records the norm-transitivity containment used in the proof. The result makes no assertion of existence for a prescribed subgroup and does not depend on the norm-subgroup existence theorem or a completed reciprocity map. Its provenance is the published local class formation, the derived finite norm-index support, and Mathlib's finite Galois correspondence and subgroup index results; it introduces no new literature claim.
