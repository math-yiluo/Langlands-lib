# Admissibility tests on a cofinal family of open subgroups

`Langlands.AdmissibleCofinalStatement` explicitly quantifies a Noetherian
instance on the commutative coefficient ring and a set `S` of open
subgroups. Its hypothesis says that every open subgroup `K` contains
some `L` belonging to `S`. Under this hypothesis it asserts, for every
representation `rho`, that admissibility is equivalent to smoothness
together with finite generation of the fixed-vector module for every
member of `S`.

The direction of cofinality is toward smaller subgroups. The family need
not be countable and need not consist of compact subgroups. The theorem
does not supply compact-open cofinality or cofinality of a congruence family.
The group needs a topology; continuity of group operations is not required.
There is no topology on the representation module.

## Provenance

This is an internal consequence of Casselman's all-open-subgroup
admissibility definition in Chapter II, Section 1, page 2, first paragraph.
If `L` is contained in `K`, the `K`-fixed module is a submodule of the
`L`-fixed module. Over Noetherian coefficients, finite generation of the
latter implies finite generation of the former. Cofinality supplies such
an `L` for every open `K`. The target is not attributed to a separately
numbered source theorem.

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019.
- Actual PDF:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Exact dependency and status

The only project import of this statement is
`Langlands.Representation.Smooth.Definitions`, artifact
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1. Its published Lean SHA256 is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`
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
Worker 0 authored the original target and this separation into modules.
