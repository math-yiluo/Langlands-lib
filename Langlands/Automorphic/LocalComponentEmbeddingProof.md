# Embedded irreducible representations are local components

`Langlands.Automorphic.localComponentEmbedding` proves
`Langlands.Automorphic.LocalComponentEmbeddingStatement.{u, uW}`. The universe
`u` is that of the number field `F`, and `uW` is that of the candidate local
carrier. For an irreducible jointly admissible operator subquotient `Q` of
`GL_(r+1)` over `F`, isotypy for an irreducible local representation is
equivalent to the existence of a nonzero intertwining map from that
representation to `Q` at the given place.

At a finite place the intertwining maps are for `GL_(r+1)(F_v)`. At a real place
they intertwine both `O(r+1)` and the complexified Lie algebra of `GL_(r+1)(ℝ)`.
At a complex place the two actions are those of `U(r+1)` and the complexification
of the real Lie algebra of `GL_(r+1)(ℂ)`. At both infinite places irreducibility
means irreducibility for the two actions together. The candidate local
representation is subject only to the applicable irreducibility condition.

## Proof

The theorem applies `localComponentEmbedding_of_localComponentExistence` to the
published `localComponentExistence`. The latter supplies an
irreducible isotypic type `A` at each place. The proof compares the candidate
local representation with `A` using intertwiners between their carriers.
[Local component existence](LocalComponentExistenceProof.md)

A nonzero intertwiner from an irreducible representation has simple image. Since
the images of the maps from `A` span the restriction of `Q`, Mathlib's
`Submodule.linearEquiv_of_sSup_eq_top` identifies that simple image with one of
the images from `A`. Precomposition with the resulting isomorphism preserves
those images and therefore transfers isotypy to the candidate representation.
For the other direction, the ranges of zero maps cannot span the nonzero space
`Q.Space`. At an infinite place a free-monoid representation encodes both
actions and allows the same argument. [Reduction to local component existence](LocalComponentEmbeddingReduction.md)

## Provenance

This is the derived embedding criterion from §4 of the statement's Markdown.
The proof follows §7, item 2, which expands Flath's use of isotypic restriction
to justify factor uniqueness at the end of the proof of Theorem 1. The source
is D. Flath, *Decomposition of representations into tensor products* (1979),
p. 180 (PDF p. 176), registered as `flath-1979-tensor-products`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
[Published statement and proof route](OperatorSubquotientLocalComponentStatement.md)

The existence input uses the isotypic restriction formulation of the existence
of local factors in Flath, Theorem 3, p. 181 (PDF p. 177), and J. R. Getz and
H. Hahn, *An Introduction to Automorphic Representations* (2024), Theorem 6.3.7,
pp. 165–166 (PDF pp. 179–180). The latter is registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
[Local component existence proof and its sources](LocalComponentExistenceProof.md)
