# Admissibility in a short exact sequence

`Langlands.AdmissibleShortExactStatement` is a proposition definition. It
quantifies three actual complex representations on independently universed
modules, an injective intertwiner `i`, and a surjective intertwiner `p`.
The equality of the image of `i` and the kernel of `p` expresses exactness at
the middle module. If that middle representation is smooth, the proposition
says it is admissible if and only if both end representations are admissible.
Admissibility includes smoothness and finite generation of fixed vectors for
every open subgroup, using the existing project definition.

The group is a topological group. The explicit additional hypothesis says
every open subgroup contains a compact open subgroup. No topology or finite
dimension is imposed on any representation module. Coefficients are complex;
this statement does not claim fixed-vector exactness over arbitrary rings.
The universes of the group and the three modules are independent.

## Original source and reformulation

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II, *Smooth representations*, revision June 16, 2019:
Corollary II.1.4, printed/PDF page 4, with the short exact sequence and
smooth-middle hypothesis of Proposition II.1.3 immediately above it.
The definitions of smoothness and admissibility are in Section 1, page 2;
the stronger ambient conventions are on page 1. These passages were read
in the original, and page 4 was also inspected visually.

- Literature ID: `casselman-2019-smooth-representations`.
- Original PDF SHA256:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Actual source:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

This is a derived reformulation with complex coefficients. Casselman assumes
a locally profinite group with countability conditions and a commutative
Noetherian rational coefficient ring. The target retains precisely the
compact-open cofinality needed for the usual argument. For a compact open
subgroup, averaging gives exactness of fixed vectors; finite-dimensionality
is equivalent to finite-dimensionality of both ends of an exact sequence.
Cofinality then passes from compact open subgroups to every open subgroup,
since a larger subgroup has a subspace of the fixed vectors of a smaller one.
These observations explain the weaker group hypotheses; they are not proofs
assumed in the proposition definition. Proving this target remains separate.

This target extends the existing injective admissibility and smoothness
transfer statements with the quotient and extension conclusions. It does
not redeclare their targets or the compact-averaging/fixed-vector-surjectivity
construction. A later proof should reuse their accepted exact versions.

## Exact dependencies and scope

The sole project import is `Langlands.Representation.Smooth.Definitions`,
accepted artifact `665022df-625b-44ae-9dbd-425f6e266bab`, version 1.
Its effective Lean SHA256 is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`,
and Markdown SHA256 is
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
It was published at `10c81beaaff024987cf2945c64d0c9511f6cb686`;
fresh inspection confirms current availability and no unavailable
dependencies at Library head `d0f5322f745425b08ae8e72c1031206f45cb049e`.
Mathlib supplies the representation, intertwiner, image, and kernel types.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 8 authored this statement and explanation. This is one foundational
target within the broader induction/Jacquet/classification statement task;
it neither completes that task nor proves this proposition. Independent
statement acceptance and publication are separate from later proof acceptance.
