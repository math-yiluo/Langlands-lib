# Maps and equivalences on subgroup-fixed vectors

For a subgroup `K` of `G` and a Mathlib intertwiner `f : rho -> sigma`,
`Langlands.fixedVectorsMap f K` is the linear map from the `K`-fixed vectors
of `rho` to the `K`-fixed vectors of `sigma` whose underlying function is `f`.
The definition composes the source subtype inclusion with `f.toLinearMap`,
then restricts the codomain. The codomain-membership proof is part of the
construction: equivariance gives `sigma(k)(f(v)) = f(rho(k)(v)) = f(v)`.

For a representation equivalence `e`, `Langlands.fixedVectorsEquiv e K`
is the linear equivalence obtained by restricting `e` and its inverse.
Its inverse fields follow from the original equivalence identities, by
injectivity of subtype inclusion. The definitions impose no surjectivity
claim for fixed vectors of an arbitrary surjective intertwiner.

The coefficient ring is commutative, `G` is a group, and the representation
spaces are modules that may occupy independent universes. There is no
topology, smoothness, admissibility, finite-generation, Noetherian, or
subgroup-normality hypothesis.

## Source and existing interfaces

These are internal algebraic constructions from the fixed-vector definition
in Casselman, Chapter II, Section 1, page 2, first paragraph. They are not
translations of separately numbered source results. The fixed-vector
condition alone and the equivariance of an intertwiner justify their
generality beyond Casselman's ambient locally profinite setting.

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019, Section 1, page 2.
- Actual PDF:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The Mathlib audit located `Rep.invariantsFunctor` in
`Mathlib/RepresentationTheory/Invariants.lean`, lines 248-259 at commit
`5ed2965256430c3649e86755f9576b54eca72435`. Its map uses the same subtype
composition and codomain restriction. This interface works directly with
`Representation.IntertwiningMap` and `Representation.Equiv`, retaining
independent universes for the two representation spaces. It reuses Mathlib's
linear-map and linear-equivalence structures.

## Exact project dependency

The only project import is `Langlands.Representation.Smooth.Definitions`,
accepted artifact `665022df-625b-44ae-9dbd-425f6e266bab`, version 1,
published at commit `10c81beaaff024987cf2945c64d0c9511f6cb686`.
Its Lean SHA256 is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`
and its Markdown SHA256 is
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
The independent review receipt is `a26076cd-7da3-4621-992f-5c0207f7fe1e`.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at the commit above. Worker 0 authored these definitions.
Their defining membership and inverse proofs are included in the constructions;
the separately stated algebraic laws require their own proof review.
