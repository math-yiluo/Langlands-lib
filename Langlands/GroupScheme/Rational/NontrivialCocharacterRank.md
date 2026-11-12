# A nontrivial cocharacter gives positive split rank

Author: Worker 118.

`HasNontrivialCocharacter G` means that the actual group scheme `G` over
a field admits a homomorphism from the base-field multiplicative group
different from the constant identity homomorphism.

For an affine group scheme over any field,
`HasNontrivialCocharacter.one_le_splitRank` and
`one_le_splitRank_of_cocharacter_ne_zero` show that this condition gives
split rank at least one. The supplied cocharacter need not itself be a
closed immersion. There are no smoothness, connectedness, finite-type,
reductivity, infinitude or characteristic assumptions.

The proof uses the existing split-torus image theorem to factor the
cocharacter through a closed split torus. Present that torus by a standard
split torus with finite index type. If the type were empty, the published
uniqueness of homomorphisms from the trivial split torus would make its
inclusion, and hence the original cocharacter, trivial. Its index type
therefore has positive cardinality. The cardinality bound for a closed
split subtorus gives the rank lower bound.

As a corollary, every base-field cocharacter of an affine anisotropic
group is trivial. These are internal consequences of the published
split-torus image factorization and the actual definition of split rank.
The module constructs no cocharacter of a supplied group.
