# Fixed vectors of smooth parts: implemented proof

`Langlands.smoothPartFixedVectors` proves the complete accepted proposition
`Langlands.SmoothPartFixedVectorsStatement`. Worker 0 authored the supplied
proof and its three component lemmas. Worker 54 verified its dependencies and
implementation, expanded this explanation, and prepared the bound contribution.

`smoothPartFixedVectorsEquiv_apply` is proved by `rfl`: the equivalence's
forward constructor forgets the smoothness witness and retains `v.val.val`.
`smoothPartFixedVectorsEquiv_symm_apply` is also proved by `rfl`: the inverse
retains `v.val` and uses the given open subgroup `K` as the witness of smoothness.

`smoothPartFixedVectorsEquiv_natural` uses `ext v` to reduce equality of linear
maps to equality of the underlying vectors, including the fixed-vector subtype
coercion. Both paths through the square send `v` to `f v.val.val`, because
`smoothMap` and `fixedVectorsMap` restrict the original intertwiner without
changing its values. The remaining equation is `rfl`. The same `K` appears in
both paths.

The closing theorem uses `omit [IsTopologicalGroup G]` and then `intro _` to
introduce the instance quantified inside the proposition. It assembles the
three component lemmas as the required conjunction. The four universes for
`R`, `G`, `V`, and `W` remain independent. Coefficients are an arbitrary
commutative ring; neither original representation is assumed smooth. There
are no compactness, finite-generation, admissibility, or averaging assumptions.

The sole project import is [the target](FixedVectorsStatement.md). No prior
project proof theorem is imported, and no placeholder or new axiom is introduced.

This proof is internal to those definitions. Casselman's underlying smoothness
convention is Chapter II, Section 1, page 2, first two paragraphs,
`casselman-2019-smooth-representations`, SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The original PDF was read at pages 1-2, with its exact hash verified. It supplies
the open fixing subgroup convention and stability of the smooth subspace; these
value and naturality laws are internal consequences of the accepted constructions,
rather than a separately numbered theorem in that source. Casselman's stronger
ambient hypotheses are not used in this proof.

## Exact target and dependencies

The accepted target is `d42c7a18-e1b0-4fb0-bd39-7d311c5b5d72` version 1,
`Langlands.SmoothPartFixedVectorsStatement`, with fingerprint
`8c0c0c49f1acb0e97ad88dc7a06b32341100baaea03f8f0c4ca3cfd80a8bb2e4`. It was published at
`9db46907db3181b0c1dfd287b8ab2f1f02054cab` and is current at
`5bc58c2525e0499012801c80f17b6a9c04d57263` when this contribution was prepared.
Its independent semantic receipt is
`cc6d34baff1c435c917b8003e911577e`. All 10 effective
target and dependency source files match the workspace and their effective
published hashes. The exact definition closure is:

- `665022df-625b-44ae-9dbd-425f6e266bab` version 1:
  `Langlands.Representation.Smooth.Definitions`.
- `7ad85b8b-caae-4345-ac1b-2c2d551dbb94` version 1:
  `Langlands.Representation.Smooth.FixedVectors.Definitions`.
- `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` version 1:
  `Langlands.Representation.Smooth.SmoothPart.Definitions`.
- `8bf36df6-8b13-4713-89e0-7d2ba5aa6824` version 1:
  `Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`.

Each is accepted, published, and current at that Library head. The environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1: Lean 4.34.0
at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib
at `5ed2965256430c3649e86755f9576b54eca72435`.

The Lean source is unchanged from Worker 0's public draft, revision 1,
key `6cd1729ce6bd81b881ea551a37d5359c72e569ba9da53b57a6e18e70a09f2e28`.
The exact proof task is `60ac5cf7-bce0-49c5-a64a-d4c6374e7d2e`, revision 1.
Machine validation uses shared incremental Lake compilation and exact target
inspection, including allowed assumptions. Independent semantic review and
current Library publication are separate requirements; compilation alone does
not establish either.
