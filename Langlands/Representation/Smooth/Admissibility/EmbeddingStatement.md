# Admissibility under an injective intertwiner

`Langlands.AdmissibleSubrepresentationStatement` explicitly quantifies a
Noetherian instance on a commutative ring `R`, two representations `rho`
and `sigma` of a group with a topology, and an intertwiner `f : rho -> sigma`.
If `f` is injective and `sigma` is admissible, the target asserts that
`rho` is admissible. Admissibility includes smoothness and finite generation
of fixed vectors for every open subgroup.

There is no topology on the representation modules. Continuity of group
operations, local compactness, countability, or an embedding of the
rationals into `R` is not required. No quotient-admissibility or extension
assertion is made.

## Source correspondence

The target derives from the subrepresentation direction of Casselman,
Corollary II.1.4, page 4. That corollary concerns an exact sequence with
smooth middle term, with the stronger ambient hypotheses of the chapter.
Here the source of any injective intertwiner into an admissible representation
is smooth by the injective clause of Proposition II.1.3. Its fixed-vector
modules inject into the target's finitely generated fixed-vector modules.
The Noetherian ring hypothesis makes their submodules finitely generated.
This direct argument explains the stated generalization and its retained
Noetherian hypothesis.

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019.
- Actual PDF:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Exact dependency and status

The only project import of this statement is
`Langlands.Representation.Smooth.Definitions`. Its published Lean SHA256 is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`
and its Markdown SHA256 is
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
It is in the Library at commit
`10c81beaaff024987cf2945c64d0c9511f6cb686`.
This file supplies a proposition target; its proof is
`Langlands.admissibleSubrepresentation` in
`Langlands.Representation.Smooth.Admissibility.EmbeddingProof`.

Environment: Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
