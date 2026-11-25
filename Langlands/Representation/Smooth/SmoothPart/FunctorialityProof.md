# Functoriality of the smooth part

This proof establishes `Langlands.SmoothPartFunctorialityStatement`. The closing
theorem is `Langlands.smoothPartFunctoriality`. All four component lemmas and the
closing theorem belong to this single module. Its exact dependencies were checked.

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
   the subtype inclusion. The construction applies `ofBijective` to
   `smoothInclusion`, which retains its forward function. The formula is
   definitionally true and is proved by `rfl`.

The closing theorem introduces the topological-group instance quantified inside
the proposition, then packages these four lemmas as its conjunction.
The `omit [IsTopologicalGroup G]` declaration prevents an additional external
topological-group assumption on the closing theorem.

## Scope

The coefficient ring is any commutative ring. The ring, group, and three modules
have five independent universes. Each module has its own additive commutative
group and module structure. The first three laws hold for arbitrary
representations and intertwiners; only the equivalence formula assumes
`IsSmooth ρ`. No topology on the modules, compactness, finiteness, or admissibility
is assumed.

## Dependencies, preparation and provenance

The sole direct import is the target module
`Langlands.Representation.Smooth.SmoothPart.FunctorialityStatement`,
effective snapshot
`39b9a25d5d228815c343589caad8e8f7d5fb46cb2b6a898e937f8756076f41db`.
The target fingerprint is
`edaf77311a288e9fe5b050b1ca841db136c2debeacc0273b13b04e41c5fd53ef`.

Its exact transitive project dependencies are:

- Smooth-part definitions `Langlands.Representation.Smooth.SmoothPart.Definitions`,
  effective snapshot
  `2c3f418ff58c7f35ecddc9b1263ff8d24c84da8eff258221f158b8eb81f4ea61`.
- Smoothness definitions `Langlands.Representation.Smooth.Definitions`,
  effective snapshot
  `092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`.

During preparation, target and dependency availability were verified and all
six source-closure Lean/Markdown hashes matched the recorded ones. No project
proof is imported.

The source context is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, revision June 16, 2019,
Section 1, page 2, first two paragraphs: smooth vectors are fixed by an open
subgroup and form a subspace stable under the group action. Registered source
`casselman-2019-smooth-representations`, SHA-256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The four laws here are internal consequences of the constructions,
rather than separately numbered results in that passage.

The preparation environment was
Lean 4.34.0, Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation during that preparation was development evidence only. The
proof's validation against the exact target is recorded in
[FunctorialityStatement](FunctorialityStatement.md#checks).
