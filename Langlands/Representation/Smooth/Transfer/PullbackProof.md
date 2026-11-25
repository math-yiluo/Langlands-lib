# Proof of smoothness under continuous pullback

This module proves `Langlands.SmoothPullbackStatement`
from the adjacent statement module. The proof was checked against
the exact target and dependencies.

For `isSmoothVector_comp`, choose an open subgroup `K` fixing the
original vector. Mathlib's `OpenSubgroup.comap` forms its preimage under
the continuous group homomorphism. An element of this preimage acts
through an element of `K`, so the original fixing equation applies.
`isSmooth_comp` repeats this for each vector, and `smoothPullback`
closes the proposition target.

Only continuity of the homomorphism is required for this openness
argument; continuity of group operations is not used.
The source is the open-subgroup definition in Casselman, Chapter II,
Section 1, page 2, first paragraph; `literature_id`
`casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
This proof is an internal elementary derivation, not a translation of a
separately numbered source proof. [PullbackStatement.md](PullbackStatement.md)
records the actual original file and exact definition dependency.

The exact statement is `Langlands.SmoothPullbackStatement`.
Its checked proposition fingerprint is
`464c4acf021ff9e7cad37b145d53b19d96005600bb8ca39164e93d8c078ca6cb`.
The local statement pair matches the recorded bytes. The target and the
definition dependency were checked to have no missing files or unavailable
dependencies.
The sole project definition dependency is
`Langlands.Representation.Smooth.Definitions`.
The component lemmas remain in this single coherent proof module.
Native compilation and whole-target checks are development evidence.

Environment: Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
