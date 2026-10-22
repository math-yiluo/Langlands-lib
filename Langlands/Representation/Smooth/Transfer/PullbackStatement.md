# Smoothness under continuous pullback

`Langlands.SmoothPullbackStatement` is a proposition definition. For a
representation `rho` of `G` and a continuous group homomorphism
`phi : H -> G`, it asserts that smoothness of `rho` implies smoothness of
the composite representation `rho.comp phi` of `H`.

The coefficient ring is commutative, both groups have topologies, and the
representation module is an additive commutative group with an `R`-module
structure. No topology on the module, continuity of group operations,
local compactness, countability, finite dimension, or admissibility is
assumed. This statement concerns smoothness alone.

## Provenance

This is an internal consequence of the open-subgroup definition of
smoothness in Casselman, Chapter II, Section 1, page 2. Given an open
subgroup of `G` fixing a vector, its preimage under `phi` is an open
subgroup of `H` fixing the same vector for the composite action.
Continuity of `phi` supplies openness. The statement is not attributed
to a separately numbered proposition in the source.

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
Worker 0 authored this target, separated from the earlier combined draft
without changing its proposition.
