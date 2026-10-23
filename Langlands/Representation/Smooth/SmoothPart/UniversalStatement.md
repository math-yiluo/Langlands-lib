# Unique factorization through the smooth part: proposition target

`Langlands.SmoothPartUniversalProperty` is a proposition definition.
For any topological group `G`, commutative ring `R`, independently universed
`R`-modules `V` and `W`, representations `rho` on `V` and `sigma` on `W`, and
smoothness proof for `sigma`, every intertwiner `f : sigma -> rho` has a unique
intertwiner `lift : sigma -> smoothPart rho` whose composite with the inclusion
is `f`. The uniqueness quantifies equality of the bundled intertwiners.

The topological-group instance is explicitly quantified inside the proposition.
No admissibility, finite-generation, local-compactness, or topology on either
module is assumed. The only project import is the accepted
`SmoothPart.Definitions` pair and its accepted foundational dependency.

This is an internal universal property of the smooth-vector subspace described
by Casselman, not a quotation of a separately numbered result. Equivariance
makes the image of a smooth representation consist of smooth vectors; subtype
inclusion makes the factorization unique.

Source: `casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
See [Definitions](Definitions.md) for the original file, precise construction
and dependency versions, and pinned environment.

During original preparation, the preceding aggregate draft used the same
proposition name with its
topological-group instance as an external declaration parameter. This separated
target placed that instance in the proposition itself so the whole
assumption was visible in the target. This historical separation preceded
the statement acceptance below; the present correction changes no Lean target.
The original Test 2 record of the direct construction dependency is artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, independently published at
Test 2 commit `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`. Its transitive foundation is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1.

`UniversalProof.lean` implements the entire target as
`Langlands.smoothPartUniversalProperty`, introducing the topological-group
instance at its internal binder. The canonical lift supplies existence, and
subtype and intertwiner extensionality supply uniqueness. The statement defines
the proposition; the separate proof establishes it.

## Verified historical status

Both original pairs were independently accepted and published. Worker 159
checked the original Test 2 export on October 23, 2026, using the records and
byte comparison described in [Definitions](Definitions.md#verified-historical-status).
These are separate statement and proof acceptances:

| Contribution | Original candidate | Accepted original validation | Independent approval | Recorded Test 2 publication |
| --- | --- | --- | --- | --- |
| UniversalStatement, version 1 | `16500d55-deee-48eb-b34b-91e7fe62065f` | `8ae8f8a0-e2c1-4d05-9a54-7ec9461ad5c6` | Reviewer 26, `ed612220-3b7d-4722-aac7-8b1e058f92fd`, October 14, 2026 | `a28679cf25a4ce001af4e724a51fd7db72864cd3`, October 14, 2026 |
| UniversalProof, version 1 | `ab36e2ca-7530-48d6-9852-34b6a9d70ac0` | `738b0000-73b3-4750-9eea-c1b6ccd72176` | Reviewer 72, `281c1091d3e846919dd1aeb3a56db99f`, October 15, 2026 | `9db46907db3181b0c1dfd287b8ab2f1f02054cab`, October 15, 2026 |

The proof validation reports `proof_accepted=true` and successful exact-target
checking. These historical receipts establish more than source presence or
development compilation; they do not accept this later Markdown correction.
