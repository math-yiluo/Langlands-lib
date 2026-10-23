# Fixed vectors of the smooth part

Worker 0's `smoothPartFixedVectorsEquiv rho K` identifies the vectors fixed by
an open subgroup `K` in `smoothPart rho` with the vectors fixed by `K` in `rho`.
It is an `R`-linear equivalence for a commutative ring, a topological group,
and an arbitrary module representation. The original representation need
not be smooth. No compactness or finite-generation assumption is used.

The forward map forgets the smooth-vector membership proof. For the inverse,
a `K`-fixed vector is smooth because the open subgroup `K` itself witnesses
the defining predicate. Equality of the underlying vectors proves the inverse
and linearity fields. Construction proofs are contained in the definition.

This is an internal consequence of Casselman Chapter II, Section 1, page 2,
first two paragraphs, which define smooth vectors by open fixing subgroups
and their stable subspace. It supports the distinction between full and
smooth duals in Section 3, page 6, without using Proposition II.3.1's averaging
argument or asserting duality with the fixed submodule.

- Literature ID: `casselman-2019-smooth-representations`.
- Original revision: June 16, 2019.
- Content SHA:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Actual source:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The sole direct project import is `SmoothPart.Definitions`. Its original
Test 2 record is accepted artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` version 1. Its foundation
`665022df-625b-44ae-9dbd-425f6e266bab` version 1 is accepted and published.
The direct dependency's recorded Test 2 publication is
`cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`.
Original Test 2 preparation environment:
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1 pins Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verified historical status

This definition pair was independently accepted and published in Test 2 on
October 14, 2026. Worker 159 verified its original records on October 23, 2026,
using the export and byte comparison described in
[Definitions](Definitions.md#verified-historical-status):

- Original candidate: `8bf36df6-8b13-4713-89e0-7d2ba5aa6824`, version 1.
- Accepted original validation: `6b264218-ebf7-4919-a0ce-da88df8d5734`.
- Independent approval: Reviewer 42,
  `51c5f743-c16d-4e28-919b-c64311bd5224`, October 14, 2026.
- Recorded Test 2 publication:
  `a158df54c354b831c3b158cd0a299f3f78acb9da`, October 14, 2026.

The construction acceptance covers the linear equivalence and its intrinsic
inverse and linearity fields. The adjacent value formulas and naturality laws
are stated separately in `SmoothPartFixedVectorsStatement` and proved in full
by `smoothPartFixedVectors` in `FixedVectorsProof.lean`. Their separate
original records are:

| Contribution | Original candidate | Accepted original validation | Independent approval | Recorded Test 2 publication |
| --- | --- | --- | --- | --- |
| FixedVectorsStatement, version 1 | `d42c7a18-e1b0-4fb0-bd39-7d311c5b5d72` | `29444ff2-4149-4659-9a1f-26a1f8649afb` | Reviewer 71, `cc6d34baff1c435c917b8003e911577e`, October 15, 2026 | `9db46907db3181b0c1dfd287b8ab2f1f02054cab`, October 15, 2026 |
| FixedVectorsProof, version 1 | `845f3f41-937b-4cd6-93ac-408338821da3` | `997582d4-ff38-42e2-a2da-611cc12605a4` | Reviewer 167, `ec2fa0110e8a4bde879fb9123be60895`, October 18, 2026 | `e4e22245747ec04edd4445d4557b746f8f53de29`, October 18, 2026 |

The proof's original validation reports `proof_accepted=true`, a Lake build,
exact-target, statement-definition and frozen-input checks. Its exported final
integration validation is a batch build with `proof_accepted=false`; the export
contains neither `archive/1/final` source files nor a final source-binding or
semantic-check record for this proof. Thus the original acceptance and recorded
publication are verified, and the pilot pair matches the original accepted
bundle, but an archived-final-byte comparison and a fresh final exact-target
receipt are not established by this export. This limit does not undo the
original acceptance. The historical records do not accept this later Markdown
correction.
