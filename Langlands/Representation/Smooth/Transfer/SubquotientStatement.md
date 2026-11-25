# Smoothness under injective and surjective intertwiners

`Langlands.SmoothSubquotientStatement` is a proposition definition. It
quantifies over representations `rho` and `sigma` on two modules and an
intertwiner `f : rho -> sigma`, and asserts both of the following:

- If `f` is injective and `sigma` is smooth, then `rho` is smooth.
- If `f` is surjective and `rho` is smooth, then `sigma` is smooth.

The coefficient ring is commutative. The group carries a topology, and the
modules are additive commutative groups with compatible scalar actions.
There is no topology on either module. The fixing subgroup may depend on
the vector. Continuity of group operations, local compactness, countability,
Noetherianity, and finite dimension are not assumed.

These conclusions express smoothness inheritance by subrepresentations and
quotients using maps rather than a particular bundled submodule or quotient.
They make no assertion about surjectivity on fixed-vector modules.

## Source correspondence

The target is derived from the smoothness clause of Casselman,
Proposition II.1.3. That proposition starts with an exact sequence
`0 -> U -> V -> W -> 0`, assumes `V` smooth, and concludes that `U` and `W`
are smooth. Its subsequent compact-open fixed-vector exactness assertion
is outside this target. Injectivity and surjectivity suffice for the two
separate smoothness implications, so no exactness condition linking them
is needed here.

The chapter imposes locally profinite and countability hypotheses and a
commutative Noetherian ring containing the rationals. The selected clause
has a direct proof using only open fixing subgroups, equivariance, and
injectivity or surjectivity. The broader hypotheses in Lean reflect this
specific generalization, not the full scope of the source proposition.

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019, Proposition II.1.3, page 4,
  first sentence before the fixed-vector exact sequence.
- Actual PDF:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Exact dependency and status

The only project import is `Langlands.Representation.Smooth.Definitions`.
Its Lean SHA256 is `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`
and its Markdown SHA256 is
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`;
its effective snapshot is
`092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`.
This file supplies a proposition target; the proof is
`Langlands.smoothSubquotient` in
`Langlands.Representation.Smooth.Transfer.SubquotientProof`.

Prepared environment: Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
