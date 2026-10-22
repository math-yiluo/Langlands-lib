# Proof of admissibility under representation equivalence

Worker 0 authored the complete Lean proof. Worker 17 checked the exact accepted
target, definitions and shared proof, and prepared this contribution. Both
workers are recorded as coauthors. The Lean source is unchanged from Worker 0's
shared draft.

`isAdmissible_of_equiv` chooses a preimage of each target vector using the
linear equivalence, chooses an open subgroup fixing that preimage, and
transports its fixing equations through equivariance. This proves smoothness
directly inside the consuming proof. For every open subgroup, `fixedVectorsEquiv`
restricts the representation equivalence, and
`Module.Finite.equiv_iff` transports finite generation.
Applying the same argument to the inverse equivalence proves
`isAdmissible_iff_of_equiv`. The final theorem `admissibleEquivalence`
closes the adjacent proposition target.

The proof does not use Noetherianity or continuity of group operations.
The coefficient, group, source-module and target-module universes are independent.
The topology is only on the group; the modules are arbitrary.
[EquivalenceStatement.md](EquivalenceStatement.md) records the precise
provenance from Casselman's admissibility definition on page 2.

## Dependency and validation status

The exact statement is
`b844a6ce-e7d4-4e71-8bd3-8a80abb57ba0`, version 1, independently accepted
and published at commit `1f65af808ff73b87aa55579d790da666ded237f5`,
with receipt `3665ccc6-d2ba-4786-ba9c-0d4e04752532`.
Its target fingerprint is
`734940f0341c203f8ec56bf0eb38548d2cd02b0ee670593189e29ccd6363680d`.
The accepted statement's Lean and Markdown SHA-256 values are respectively
`e92b32efdaf676556953406f3306fc45d32e685a5f0aa0de1bbe1d9ee0245574` and
`a246a8409fb5a769a3324c3b8ba305c1a5c8e2db2797a31176ee311f4b3b57e5`.
Its construction import is `FixedVectors.Definitions`, artifact
`7ad85b8b-caae-4345-ac1b-2c2d551dbb94`, version 1, published at
`18d2c44b3fecb756a7634ce0f766fdc16b539b45`, with receipt
`7f5084d1-9e75-445b-b031-b754e38c4830`. Both use the foundational
definitions `665022df-625b-44ae-9dbd-425f6e266bab`, version 1,
published at `10c81beaaff024987cf2945c64d0c9511f6cb686`.
Fresh registry fetches confirmed that all three exact artifacts remain accepted,
public and current, with no missing or changed files or unavailable dependencies.
The full final reviews of the target and fixed-vector equivalence construction
were read, and local source pairs were compared with their effective hashes.
No pending project proof is imported. The component lemmas and closing theorem
stay in this one contribution. Compilation is development evidence only;
formal proof acceptance requires the exact-target task, registered independent
checker, independent semantic review, and publication.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
