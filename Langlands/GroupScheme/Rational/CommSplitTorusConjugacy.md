# Conjugacy restricted from commutative overgroups

Worker 1356. This module is an internal construction from the published
largest-split-subtorus universal property and subgroup-conjugacy laws.
It assumes no additional result from the literature.

For an affine commutative group scheme `H` locally of finite type over an
arbitrary field, `IsMaximalSplitTorus.isoOverCommGroup hi hi'` constructs
an isomorphism between the sources of any two maximal split tori in `H`.
Its composite with the second embedding is the first embedding. The
construction uses `IsMaximalSplitTorus.isLargestSplitSubtorus` and
`IsLargestSplitSubtorus.unique`: both embeddings represent the same
universal factorization property for all homomorphisms from split tori.
The theorem `subgroupConjugate_of_commGroup` consequently supplies their
rational conjugacy, with conjugating point equal to the identity.

The final theorem treats maximal split tori of an arbitrary affine group
scheme locally of finite type, when their embeddings factor through two
commutative closed subgroups that are rationally conjugate. Closedness
makes the factor maps maximal split tori in their respective overgroups.
It also gives affineness and local finite type of the second overgroup.
After transporting the first factor map across the given overgroup
isomorphism, both are maximal split tori of that commutative group.
The preceding result proves conjugacy there; the published
`SubgroupConjugate.of_overgroups` then supplies conjugacy in the ambient
group.

All statements retain finite and imperfect fields and all characteristics.
Neither smoothness nor connectedness is needed for this restriction
argument. The module does not establish existence of the commutative
overgroups or their rational conjugacy in a solvable group, so it does
not by itself prove
`SolvableMaximalSplitTorusConjugacyStatement`. It supplies the formal
restriction step needed after those geometric inputs are proved.
