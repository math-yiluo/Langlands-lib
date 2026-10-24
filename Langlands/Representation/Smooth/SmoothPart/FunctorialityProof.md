# Functoriality of the smooth part

The original proof was independently accepted and published in Test 2 on
October 15, 2026. The exact validation, independent approval and publication
records, verified on October 23, are in
[FunctorialityStatement](FunctorialityStatement.md#verified-historical-status).
The preparation accounts, artifact IDs, environment and commits below are
historical Test 2 records, distinct from the later pilot documentation correction.

This proof establishes `Langlands.SmoothPartFunctorialityStatement`, accepted
statement artifact `80ed7208-2a32-4a3f-b295-66c8a37f919a`, version 1. The closing
theorem is `Langlands.smoothPartFunctoriality`. All four component lemmas and the
closing theorem belong to this single contribution.

Worker 0 supplied the complete proof in shared draft revision 1, content key
`05202effea62060ec40434c2617ff8bbf1b5b1d114b109920ad3b4792ab45d42`.
Worker 31 checked the exact published dependencies and prepared this submission.
The proof terms are unchanged from Worker 0's draft.

## Implemented argument

`smoothMap f` restricts the underlying linear map of an intertwiner `f` to the
smooth-vector submodules. Its value has underlying vector `f v`.

1. `smoothInclusion_comp_smoothMap` proves the inclusion square commutes.
   Intertwiner extensionality reduces the equation to a vector; both sides
   evaluate to `f v`, so `rfl` closes the goal.
2. `smoothMap_id` proves identity preservation. Extensionality reduces to equality
   of underlying vectors, and the restricted identity evaluates to the original
   vector.
3. `smoothMap_comp` proves composition preservation. After extensionality, both
   sides evaluate to `g (f v)`. The order is Mathlib's `g.comp f`.
4. `smoothEquiv_apply` proves that the forward function of `smoothEquiv hρ` is
   the subtype inclusion. The accepted construction applies `ofBijective` to
   `smoothInclusion`, which retains its forward function. The formula is
   definitionally true and is proved by `rfl`.

The closing theorem introduces the topological-group instance quantified inside
the accepted proposition, then packages these four lemmas as its conjunction.
The `omit [IsTopologicalGroup G]` declaration prevents an additional external
topological-group assumption on the closing theorem.

## Scope

The coefficient ring is any commutative ring. The ring, group, and three modules
have five independent universes. Each module has its own additive commutative
group and module structure. The first three laws hold for arbitrary
representations and intertwiners; only the equivalence formula assumes
`IsSmooth ρ`. No topology on the modules, compactness, finiteness, or admissibility
is assumed.

## Dependencies, historical preparation and provenance

The sole direct import is the accepted target module
`Langlands.Representation.Smooth.SmoothPart.FunctorialityStatement`.
Its version 1 was published at commit
`672a1bfbca2444507019dc6764810d0c0bcb81e5`, effective snapshot
`39b9a25d5d228815c343589caad8e8f7d5fb46cb2b6a898e937f8756076f41db`,
with semantic publication receipt `0bbecfbd-08f8-4f0e-a83e-dd6a6d423711`.
The accepted target fingerprint is
`edaf77311a288e9fe5b050b1ca841db136c2debeacc0273b13b04e41c5fd53ef`.

Its exact transitive project dependencies are:

- Smooth-part definitions `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1,
  published at `cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, effective snapshot
  `2c3f418ff58c7f35ecddc9b1263ff8d24c84da8eff258221f158b8eb81f4ea61`.
- Smoothness definitions `665022df-625b-44ae-9dbd-425f6e266bab`, version 1,
  published at `10c81beaaff024987cf2945c64d0c9511f6cb686`, effective snapshot
  `092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`.

During original preparation, Worker 31 verified target and dependency
availability at Test 2 commit
`bb596ce619f2174816281f508cce65b3303beeb4` and matched all six source-closure
Lean/Markdown hashes to the published binding. No project proof is imported.

The source context is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, revision June 16, 2019,
Section 1, page 2, first two paragraphs: smooth vectors are fixed by an open
subgroup and form a subspace stable under the group action. Registered source
`casselman-2019-smooth-representations`, SHA-256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The four laws here are internal consequences of the accepted constructions,
rather than separately numbered results in that passage.

The original preparation environment was artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0, Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation during that preparation was development evidence only. The
original acceptance and publication came from the separate registered proof
validation `5d8f864d-330e-43c0-b26e-519dbaa668ff`, independent approval and
Test 2 publication recorded in
[FunctorialityStatement](FunctorialityStatement.md#verified-historical-status);
the earlier unavailable proof check `068d657a-0ad3-43cc-8d72-256152fea878`
supplied no acceptance evidence. Neither those historical records nor source
compilation accepts this later Markdown correction.
