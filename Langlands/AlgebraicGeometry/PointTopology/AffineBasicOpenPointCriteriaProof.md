# Basic open subschemes and points over a topological ring: proof

Authors: Worker 3519 (proof draft), Worker 158 (verification and submission).

`Langlands.AlgebraicGeometry.PointTopology.affineBasicOpenPointCriteria` proves exactly
`AffineBasicOpenPointCriteria` from `AffineBasicOpenPointCriteriaStatement`, in its original
universe and generality: every commutative ring `R`, every commutative topological ring `S`
that is an `R`-algebra, and all four clauses. No hypothesis is added. The statement records
the opening discussion of Section 3 of Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed pp.3–4, registered as
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The proof works directly with the Library's algebra points `AlgPoint R A S` and their
evaluation topology, and with the Library's localization point comparisons in
`PointTopology.Localization`. It follows the route in the statement's Markdown.

## Clause 1: the image is the unit locus

`range_basicOpenPointMap`. The map `basicOpenPointMap R S A f` is precomposition with the
localization map `A → A_f`, and `IsScalarTower.toAlgHom` (used by the statement) is
`Algebra.algHom` (used by the Library) by definition. The Library lemma
`AlgPoint.range_precomp_localization` identifies the image of precomposition with any
localization at `M` as the points unit-valued on all of `M`. For `M` the powers of `f`,
`AlgPoint.unit_powers_iff` reduces this to `IsUnit (p f)`. This holds for every `R`-algebra
`A`, with no finiteness and no topology.

## The affine line

The forward directions of clauses 2–4 apply the hypothesis to `A = R[X]`, here
`MvPolynomial Unit R` (finite type over `R`), and `f = X`.

- `lineCoordinateHomeomorph`: evaluation at `X` is a homeomorphism from the points of
  `R[X]` to `S`. It is the Library's `AlgPoint.polynomialPointHomeomorph Unit` followed by
  Mathlib's `Homeomorph.funUnique Unit S`.
- `AlgPoint.polynomialAwayUnitHomeomorph R S` (Library) is a homeomorphism from the points of
  `R[X]_X` to `Sˣ` with Mathlib's units topology, sending a point to the unit with value the
  image of `X` and inverse the image of `1/X`.
- `unitsVal_eq_basicOpenPointMap`: `Units.val` equals the composite of the inverse of the
  second homeomorphism, `basicOpenPointMap R S R[X] X`, and the first homeomorphism. Both
  sides send `u` to the value of `X` at the point `aeval u` (by
  `polynomialAwayUnitEquiv_symm_algebraMap` and `MvPolynomial.aeval_X`).

## Clause 2: openness

- Forward (`isOpen_units_of_isOpen_range_basicOpenPointMap`): by clause 1 the image for
  `R[X]` and `X` is `{p | IsUnit (p X)}`. It is the preimage of `{s | IsUnit s}` under
  `lineCoordinateHomeomorph`, and preimages under a homeomorphism are open exactly when the
  sets are open.
- Backward (`isOpen_range_basicOpenPointMap_of_isOpen_units`): by clause 1 the image is the
  preimage of `{s | IsUnit s}` under evaluation at `f`, which is continuous
  (`AlgPoint.continuous_eval`). This direction holds for every `A`, not only finite-type ones.

## Clause 3: embeddings

- Forward (`isEmbedding_unitsVal_of_isEmbedding_basicOpenPointMap`): by
  `unitsVal_eq_basicOpenPointMap`, `Units.val` is the embedding `basicOpenPointMap R S R[X] X`
  composed on both sides with homeomorphisms, hence an embedding.
- Backward (`isEmbedding_basicOpenPointMap_of_isEmbedding_unitsVal`): the Library lemma
  `AlgPoint.isEmbedding_precomp_localization` for the powers of `f`. Its proof writes every
  element of `A_f` as `a · (1/f)^n` and uses continuity of inversion on `Sˣ`, transported to
  the subspace topology by the embedding hypothesis. It needs only continuity of
  multiplication, which `IsTopologicalRing S` supplies, and holds for every `A`.

## Clause 4: open embeddings

- Forward (`isOpenEmbedding_unitsVal_of_isOpenEmbedding_basicOpenPointMap`): an open
  embedding is an embedding with open image, so the forward directions of clauses 3 and 2
  give that `Units.val` is an embedding and that its image `{s | IsUnit s}` is open.
- Backward (`isOpenEmbedding_basicOpenPointMap_of_isOpenEmbedding_unitsVal`): an open
  embedding `Units.val` is precisely Mathlib's class `IsOpenUnits S`, under which the Library
  lemma `AlgPoint.isOpenEmbedding_precomp_away` makes precomposition with any localization
  away from one element an open embedding. This direction also holds for every `A`.

## Assembly

`affineBasicOpenPointCriteria` introduces `R`, `S` and their instances and assembles the
four clauses from the lemmas above. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
