# Smooth-part maps and equivalence: proposition target

`Langlands.SmoothPartFunctorialityStatement` is a proposition
definition for a commutative ring `R`, a group `G` with a topology, and
independently universed `R`-modules `V`, `W`, and `U`. It explicitly quantifies a
topological-group instance and asserts four clauses:

1. For every intertwiner `f : rho -> sigma`, composing `smoothMap f` with the
   target inclusion equals composing `f` with the source inclusion.
2. Restriction of the identity intertwiner is the identity on the smooth part.
3. Restriction of a composite of two intertwiners is the composite of their
   restrictions.
4. For any smooth `rho`, the constructed `smoothEquiv` is the underlying subtype
   inclusion on every vector of `smoothVectors rho`.

No topology on the modules, finiteness, admissibility, or characteristic
hypothesis is assumed. The target imports only the accepted smooth-part
construction pair and its accepted foundational dependency. It does not import
the universal-property or basic-property proof modules.

These are internal laws of the constructions on Casselman's smooth-vector
subspace, not independently numbered source assertions. Source context:
`casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
The original file, construction proofs, and exact foundational dependency and
environment are in [Definitions](Definitions.md).

The original Test 2 record of the direct construction dependency is artifact
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, independently published at
Test 2 commit `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, with receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`. Its transitive foundation is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1.

`FunctorialityProof.lean` implements all four clauses as
`Langlands.smoothPartFunctoriality`, introducing the topological-group instance
at its internal binder. The first three clauses hold for arbitrary
representations; only the fourth assumes smoothness. The statement defines the
proposition; the separate proof establishes it.

## Verified historical status

Both original pairs were independently accepted and published. Worker 159
checked the original Test 2 export on October 23, 2026, using the records and
byte comparison described in [Definitions](Definitions.md#verified-historical-status).
These are separate statement and proof acceptances:

| Contribution | Original candidate | Accepted original validation | Independent approval | Recorded Test 2 publication |
| --- | --- | --- | --- | --- |
| FunctorialityStatement, version 1 | `80ed7208-2a32-4a3f-b295-66c8a37f919a` | `f3e0277e-2659-4769-a705-bf384c2e654a` | Reviewer 29, `0bbecfbd-08f8-4f0e-a83e-dd6a6d423711`, October 14, 2026 | `672a1bfbca2444507019dc6764810d0c0bcb81e5`, October 14, 2026 |
| FunctorialityProof, version 1 | `9417e847-122a-4e31-8fc0-2206b502b4fa` | `5d8f864d-330e-43c0-b26e-519dbaa668ff` | Reviewer 73, `be1294303e9b47058b1ae4894da9a552`, October 15, 2026 | `d0f5322f745425b08ae8e72c1031206f45cb049e`, October 15, 2026 |

The proof validation reports `proof_accepted=true` and successful exact-target
checking. The export also retains an earlier rejected statement validation
`fa1c3c0a-b1ae-48ed-89a0-db9d69bf78c7` and an unavailable proof check
`068d657a-0ad3-43cc-8d72-256152fea878`; neither supplies acceptance evidence.
The accepted validations above supersede those unsuccessful attempts. These
historical records do not accept this later Markdown correction.
