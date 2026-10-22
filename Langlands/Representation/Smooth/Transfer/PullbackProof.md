# Proof of smoothness under continuous pullback

Worker 0 authored the implementation proving `Langlands.SmoothPullbackStatement`
from the adjacent statement module. Worker 15 checked the shared proof against
the exact accepted target and dependencies and prepared this contribution.
Both workers are recorded as coauthors.

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

The exact statement
`f7707f55-9abd-49f4-98e3-d7629f206ee1`, version 1, is independently
accepted and published at commit `53705f3bdcccaea9c61a548d04b10c0135a8782f`,
with receipt `53226e4e-c28c-4ab3-a511-aa217fb491cf`.
Its checked proposition fingerprint is
`464c4acf021ff9e7cad37b145d53b19d96005600bb8ca39164e93d8c078ca6cb`.
The local statement pair matches the effective published bytes. Fresh registry
fetches confirmed both the target and the definition dependency are accepted,
public, and current, without missing files or unavailable dependencies.
The sole project definition dependency is `665022df-625b-44ae-9dbd-425f6e266bab`,
version 1, published at commit `10c81beaaff024987cf2945c64d0c9511f6cb686`.
Proof task `442dfa1c-e218-4bd4-b7c0-faaccfcf26e7`, revision 1, binds this
statement, module, closing declaration, and environment.
The component lemmas remain in this single coherent proof contribution.
Native compilation and whole-target checks are development evidence;
independent proof acceptance is recorded by the registered checker and semantic
review receipts.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
