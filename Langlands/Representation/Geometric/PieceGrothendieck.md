# Exact K0 maps for the actual geometric pieces

Author: Worker 320.

`Langlands.Geometric.geometricPieceK0` is the integer-linear map induced by
the existing actual smooth geometric-piece functor between the exact
finite-length smooth Grothendieck groups of two product Levis. The construction
uses proved finite-length preservation and exactness and requires no additional
preservation premise.

Fix a prime `p`, an actual `F : PadicField.{uF} p` with supplied compatible
data `T`, any rank `n`, block shapes `B C`, a permutation `w`, source and target
refinements `S R`, and equalities identifying the two intersection Levis with
the actual refined Levis. The map has source the exact Grothendieck group of
`B.Levi F.Carrier` and target that of `C.Levi F.Carrier`. These groups use
actual smooth complex representations of finite group-algebra length and all
actual short exact sequence relations, including nonsplit sequences. The
field and carrier universes remain independent, with carriers saturated at
`max uF uV`.

The underlying functor is exactly the published
`CuspidalSupport.geometricPieceSmoothFunctor`. Its order is actual normalized
refined Jacquet restriction, source equality relabeling, inverse-conjugation
intersection transport, target equality relabeling, and actual normalized
refined induction. The normalizations are inherited unchanged: inverse
half-modulus for Jacquet restriction and positive half-modulus covariance with
right translation for induction. No character or sign is added.

## Implemented preservation and class formula

`subgroupEqualityFunctor_preservesFiniteLength` and
`subgroupEqualityFunctor_preservesShortExact` eliminate the subgroup equality
and use the corresponding properties of the identity functor. They apply to
arbitrary subgroups of a group with a topology.

`intersectionTransportFunctor_preservesFiniteLength` applies the published
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` to the inverse of
`intersectionLeviConjugation`. This is an actual surjective group equivalence.
The transported representation has the same vector space, with action
precomposed by that inverse conjugation, so its group-algebra finite length is
preserved. `intersectionTransportFunctor_preservesShortExact` uses the fact
that transport leaves each underlying linear map unchanged. These two results
apply over any commutative topological ring of matrix entries; the coefficients
of the representations are complex.

`geometricPieceSmoothFunctor_preservesFiniteLength` composes these properties
with the two published finite-length clauses of
`Parabolic.normalizedRefinedFiniteLengthExactness`.
`geometricPieceSmoothFunctor_preservesShortExact` similarly composes the
published exactness clauses, using finite-length preservation at every
intermediate step. The helper results allow an arbitrary input carrier
universe `uV`; the output carrier is `max uF uV`.

`geometricPieceK0` specializes these results to the saturated carrier universe
and applies `SmoothRep.FiniteLengthGrothendieckGroup.map`.
`geometricPieceK0_finiteLengthClass` is its actual generator formula: the class
of a finite-length input maps to the class of its actual smooth geometric
piece. It permits any proof of the output's finite length, since proof
irrelevance makes the class independent of that choice.

## Internal provenance and scope

This is an internal construction from the already-published geometric-piece,
group-conjugation, finite-length, exactness and generic K0-map interfaces.
It is not a new original-literature transcription. It does not change those
interfaces or the underlying geometric-lemma source correspondence.

All ranks, including zero, are allowed. The two concrete Levi equality proofs
are inputs to the already-existing functor; existence of those equalities or
of a geometric-lemma filtration is not asserted here. No minimal-representative,
irreducibility, admissibility, central-character or finite-dimensionality
assumption is required. The map acts on every virtual class in its source.

This module supplies no sum formula for Jacquet restriction after induction,
no natural splitting, no Aubert identity and no analytic classification.
