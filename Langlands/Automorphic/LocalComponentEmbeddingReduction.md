# Local component existence implies the embedding characterization

Proof by Worker 3657. This module supplies
`Langlands.Automorphic.localComponentEmbedding_of_localComponentExistence`,
which derives `LocalComponentEmbeddingStatement.{u, uW}` from
`LocalComponentExistenceStatement.{u}`. Here `u` is the universe of the number
field and `uW` is the independent universe of the candidate local carrier.
The entry theorem applies this reduction to the published existence proof.
[Proof of the embedding characterization](LocalComponentEmbeddingProof.md)

## Compact and Lie actions as a monoid representation

`Archimedean.gkFreeRepresentation ρ π` puts the compact action `ρ` and Lie
action `π` on the generators of `FreeMonoid (K ⊕ L)` using
`FreeMonoid.lift`. The generators from `K` act by `ρ k` and those from the
complex Lie algebra `L` act by `π X`. The construction uses the two actions
as linear operators.

`Archimedean.mem_gkHoms_iff_isIntertwiningMap` proves that a linear map
intertwines the two actions exactly when it intertwines every word in the
free monoid. Induction using `FreeMonoid.inductionOn'` proves that a map which
commutes with the generators commutes with their products. For the reverse
implication it suffices to evaluate on the generators. The maps
`gkHomsIntertwiningMap` and `toLinearMap_mem_gkHoms` retain the underlying
linear maps. Consequently `iSup_range_gkHoms_eq` and `isGKIsotypic_iff`
identify the two range suprema and the resulting isotypy predicates.
`exists_mem_gkHoms_ne_zero_iff` identifies existence of a nonzero map on both
sides.

For `Archimedean.isIrreducible_gkFreeRepresentation`, a subrepresentation is
stable under each generator, hence under both the compact and Lie actions.
`IsIrreducibleGKModule` then forces its underlying subspace to be `⊥` or `⊤`
and supplies nontriviality of the carrier. Thus the irreducibility carried
into the monoid representation is joint irreducibility. Applying
`IsotypicEmbedding.isotypic_iff_exists_ne_zero` to the free-monoid
representations gives `Archimedean.isGKIsotypic_iff_exists_ne_zero`.
[Isotypy and intertwining maps for monoid representations](../Representation/IrreducibleIsotypicEmbedding.md)

## Application at each place

For `Q : IrreducibleOperatorSubquotient F r`, the instance
`IrreducibleOperatorSubquotient.space_nontrivial` supplies a nonzero carrier.
The place-specific equivalences apply the monoid or compact-and-Lie argument
with an irreducible type for which `Q` is already isotypic.

- `finitePlaceIsotypic_iff_exists_ne_zero` uses the monoid `GL_(r+1)(F_v)`
  acting by `Q.subquotient.localRepresentation v`.
- `realPlaceIsotypic_iff_exists_ne_zero` uses the pair
  `realPlaceCompactRepresentation v` and `realPlaceLieAction v`.
- `complexPlaceIsotypic_iff_exists_ne_zero` uses the corresponding pair
  `complexPlaceCompactRepresentation v` and `complexPlaceLieAction v`.

`finitePlaceEmbedding_of_localComponentExistence`,
`realPlaceEmbedding_of_localComponentExistence` and
`complexPlaceEmbedding_of_localComponentExistence` apply those equivalences
with the types from the corresponding clauses of
`LocalComponentExistenceStatement`. At a finite place the type is
`A.obj.representation`, and `A.property.1` gives its irreducibility. At a real
or complex place the proof extracts the pair of actions and its
`IsIrreducibleGKModule` and isotypy proofs. The comparison uses only those
properties of the supplied type. The final reduction assembles the three
clauses, with the candidate carrier in universe `uW` throughout.

## Provenance

The argument follows §7, item 2, of the statement's Markdown. At the end of the
proof of Theorem 1, Flath identifies the isotypic restriction to a factor as the
reason that the restricted representation determines the local isomorphism
class. The semisimple argument implements this step, with morphisms across
carrier universes. The choice of a free monoid to encode the two archimedean
actions is specific to this formalization.
[Published statement and proof route](OperatorSubquotientLocalComponentStatement.md)

- D. Flath, *Decomposition of representations into tensor products*, Proc.
  Sympos. Pure Math. 33, Part 1, AMS, 1979, pp. 179–183. The isotypic restriction
  argument is the last sentence of the proof of Theorem 1, p. 180 (PDF p. 176).
  The adelic theorem is Theorem 3, p. 181 (PDF p. 177). Registered source
  `flath-1979-tensor-products`, SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
  Graduate Texts in Mathematics 300, Springer, 2024. Theorem 6.3.7 begins on
  p. 165 (PDF p. 179), with uniqueness of the factors on p. 166 (PDF p. 180).
  Registered source `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
