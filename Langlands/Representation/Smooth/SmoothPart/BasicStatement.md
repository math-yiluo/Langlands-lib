# Basic properties of the smooth part: proposition target

`Langlands.SmoothPartBasicStatement` is a proposition definition
depending on `SmoothPart.Definitions`. It assumes a
commutative ring `R`, a group `G` with a topology, and an `R`-module `V`, in
independent universes.

For every representation `rho`, it asserts:

1. Membership in `smoothVectors rho` is equivalent to `IsSmoothVector rho`.
2. Zero is smooth.
3. The sum of any two smooth vectors is smooth.
4. Every scalar multiple of a smooth vector is smooth.
5. `rho` is smooth if and only if `smoothVectors rho` is the whole module.
6. For every topological-group instance on `G`, smooth vectors are invariant
   under each group element, `smoothPart rho` is smooth, and its inclusion is
   the underlying subtype map and is injective.

The final group of clauses explicitly quantifies `IsTopologicalGroup G` inside
the proposition. The earlier clauses do not require this compatibility between
the group operations and topology. No topology on `V` or finiteness hypothesis
is present.

The membership and closure clauses express the actual smooth-vector submodule
described by Casselman; the smoothness characterization and properties of the
restricted representation are internal consequences of that construction.
They are not quoted as a separately numbered source theorem.

Exact source: `casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
The actual PDF, construction-field explanations, accepted foundational artifact,
and pinned environment are recorded in [Definitions](Definitions.md).

The original Test 2 record of the direct construction dependency is artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, independently published at
Test 2 commit `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`. Its transitive foundation is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1.

`BasicProof.lean` implements the entire target as `Langlands.smoothPartBasic`.
It supplies the unrestricted clauses first and introduces `IsTopologicalGroup`
only at the final conjunct's internal binder. The statement defines the
proposition; the separate proof establishes it.

## Verified historical status

Both original pairs were independently accepted and published. Worker 159
checked the original Test 2 export on October 23, 2026, using the records and
byte comparison described in [Definitions](Definitions.md#verified-historical-status).
These are separate statement and proof acceptances:

| Contribution | Original candidate | Accepted original validation | Independent approval | Recorded Test 2 publication |
| --- | --- | --- | --- | --- |
| BasicStatement, version 1 | `7101568f-3e71-4b9d-b1c5-f35546e0e8dd` | `514d9ae0-7ad9-4dc6-a8bf-6909e90592fc` | Reviewer 27, `a2c4fec7-eaaa-4396-889d-edf61fcd5156`, October 14, 2026 | `6c1028baa3f29e21f18dd147d07f4b7873a88b8c`, October 14, 2026 |
| BasicProof, version 1 | `b247128b-8881-47d1-ac8a-9d5b098e4548` | `fb8124bc-935a-46bd-8708-2424ef72ad69` | Reviewer 61, `b0087dbecfa84d449d6fecda76ccad74`, October 15, 2026 | `d0f5322f745425b08ae8e72c1031206f45cb049e`, October 15, 2026 |

The proof validation reports `proof_accepted=true` and successful exact-target
checking. These historical receipts establish more than source presence or
development compilation; they do not accept this later Markdown correction.
