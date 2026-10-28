# Actual transport of canonically permuted block tensors

Author: Worker 289.

This internal construction identifies actual whole-Levi Weyl transport of an
external block tensor with the external tensor of the reordered factors. It
uses `BlockShape.permute e`, whose target block `i` is source block `e i`,
and the canonical coordinate permutation `BlockShape.blockPermutation e`.
The field `F` is arbitrary. Its universe and the common factor-carrier universe
are independent. There are no topology, smoothness, irreducibility,
admissibility, positive-rank or finite-length premises; rank zero is included.

`eq_blockPermutation_of_blockIndex` is the geometric reduction. Given an actual
Levi-conjugating minimal permutation `w` from `B` to `C`, suppose its block
labels agree, as natural numbers, with the labels of the canonical permutation.
Then both `C = B.permute e` and `w = B.blockPermutation e`. The proof applies
the published `TotalConjugatingCount.eq_of_blockValue_eq` to the two pairs
consisting of a target shape and a minimal actual conjugating permutation.
Their block values agree by evaluating the assumed coordinate-label identity
on the first coordinate of each source block. This is a rigidity consequence
of the published uniqueness lemma, rather than a count-based argument.

The published `leviConjugation_symm_blockPermutation_apply`, imported from
[`AssociationReduction`](AssociationReduction.md), computes inverse conjugation:
at source block `e i`, it is exactly target block `i`. Its proof derives this
identity from the forward block-conjugation formula and the inverse identities
of the Levi equivalence.
`leviConjugation_symm_blockPermutation` identifies the resulting actual group
equivalence with inverse dependent-product reindexing. Both identities allow
any proof `hw` of the required actual Levi conjugation.

`blockPermutationTensorEquiv` uses the linear equivalence underlying
`FiniteTensor.reindexEquiv`. The group-equivalence identity just proved
supplies intertwining for the actual `CuspidalSupport.transport` action.
The target is the block tensor on `B.permute e` of the factors `ρ (e i)`.
These groups have the required ranks by definition, so no extra carrier or rank
transport is introduced. `blockPermutationTensorEquiv_tprod` sends the pure
tensor with coordinates `v i` to the pure tensor with coordinates `v (e i)`.
The underlying tensor equivalence includes both inverse identities.

The provenance is internal: the module combines the published uniqueness
lemma, actual Levi matrix conjugation and finite dependent tensor reindexing.
It prepares a canonical description of the tensor input for an adjacent-swap
argument. It makes no assertion about the factors or finite length of the
resulting normalized inductions.
