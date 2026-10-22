# Smooth vectors and open stabilizers

`Langlands.SmoothVectorStabilizerStatement` is a proposition definition.
For every vector `v` in a representation `rho`, it identifies
`IsSmoothVector rho v` with openness of the stabilizer subgroup
`rho.stabilizer v`.

Here `G` is a topological group, the coefficient ring is commutative, and
the representation acts on an `R`-module. The stabilizer is Mathlib's
algebraic stabilizer subgroup for the representation. No topology on the
module, continuity of the representation as a map, local compactness,
countability, finite dimension, or admissibility is assumed.

## Provenance

This is an internal consequence of Casselman's open-subgroup definition
of a smooth vector in Chapter II, Section 1, page 2. If an open subgroup
fixes a vector, it is contained in the stabilizer. A subgroup of a
topological group containing an open subgroup is open. Conversely, an
open stabilizer itself witnesses smoothness. The statement is not
attributed to a separately numbered source theorem.

The topological group hypothesis is explicit because the forward
implication uses the subgroup openness theorem. The broader group and
coefficient setting is justified by this elementary argument rather
than by applying a source theorem outside its hypotheses.
`IsTopologicalGroup G` is quantified inside the proposition value, so the
target retains that hypothesis even though it is not needed merely to
form the two predicates being compared.

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019, Section 1, page 2, first paragraph.
- Actual PDF:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Exact dependency and status

The only project import is `Langlands.Representation.Smooth.Definitions`,
artifact `665022df-625b-44ae-9dbd-425f6e266bab`, version 1. Its published
Lean SHA256 is `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`
and its Markdown SHA256 is
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
Reviewer 1 approved and published this pair without integration edits.
It is current in the Library at commit
`10c81beaaff024987cf2945c64d0c9511f6cb686`, effective snapshot
`092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`,
with independent review receipt `a26076cd-7da3-4621-992f-5c0207f7fe1e`.
This file supplies a proposition target for a separately reviewed proof contribution.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 0 authored this target and separated it from the earlier combined
draft. During target inspection, the topological-group hypothesis was
corrected to be explicitly quantified inside the proposition.
