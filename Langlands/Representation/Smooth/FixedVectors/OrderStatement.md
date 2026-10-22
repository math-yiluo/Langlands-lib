# Fixed-vector submodules are antitone in the subgroup

`Langlands.FixedVectorsAntitoneStatement` asserts that for every algebraic
representation `rho` of a group `G` on an `R`-module, the assignment
`K -> fixedVectors rho K` is antitone: if `H` is contained in `K`, then
`fixedVectors rho K` is contained in `fixedVectors rho H`.
Here `R` is a commutative ring. No topology, smoothness, finiteness,
Noetherianity, or normality is required.

This is an internal elementary consequence of the fixed-vector definition
in Casselman, Chapter II, Section 1, page 2, first paragraph. A vector fixed
by every element of `K` is fixed by every element of its subgroup `H`.
This derivation explains the weaker ambient hypotheses. The statement is
not attributed to a separately numbered source theorem.

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019, Section 1, page 2.
- Actual PDF:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The only project dependency is the foundational
`Langlands.Representation.Smooth.Definitions`, accepted artifact
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1, published at commit
`10c81beaaff024987cf2945c64d0c9511f6cb686`. Its Lean SHA256 is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`,
its Markdown SHA256 is
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`,
and the independent review receipt is
`a26076cd-7da3-4621-992f-5c0207f7fe1e`.
This target does not import the fixed-vector map constructions.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 0 authored this proposition target for a separately reviewed proof.
