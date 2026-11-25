# Fixed vectors of smooth parts: implemented proof

`Langlands.smoothPartFixedVectors` proves the complete proposition
`Langlands.SmoothPartFixedVectorsStatement`, with three component lemmas.
Its dependencies and implementation were verified.

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
value and naturality laws are internal consequences of the constructions,
rather than a separately numbered theorem in that source. Casselman's stronger
ambient hypotheses are not used in this proof.

## Exact target and preparation

The target is
`Langlands.SmoothPartFixedVectorsStatement`, with fingerprint
`8c0c0c49f1acb0e97ad88dc7a06b32341100baaea03f8f0c4ca3cfd80a8bb2e4`.
At preparation, all 10 target and dependency source files matched their
recorded hashes. The exact definition closure is:

- `Langlands.Representation.Smooth.Definitions`.
- `Langlands.Representation.Smooth.FixedVectors.Definitions`.
- `Langlands.Representation.Smooth.SmoothPart.Definitions`.
- `Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`.

The preparation environment was Lean 4.34.0
at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib
at `5ed2965256430c3649e86755f9576b54eca72435`.

The machine validation of the proof ran a Lake build and exact-target,
statement-definition and frozen-input checks.
