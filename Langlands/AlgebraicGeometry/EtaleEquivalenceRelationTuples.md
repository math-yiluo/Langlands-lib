# Finite related tuples of an étale equivalence relation

This internal helper implements the iterated fibre products that start the proof
of Stacks Project, Decent Algebraic Spaces, Lemma 68.8.3 (Tag 0BBN), and hence
Lemmas 68.8.4 and 68.8.6 (Tags 07S9 and 07ST). The sources are registered as
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. No quotient algebraic space is used
in the construction: all products are built directly from the given scheme
equivalence relation.

The index `n` denotes tuples with `n + 1` entries. `tuplePresentation` recursively
stores the representing scheme and its coordinate morphisms. It starts with
`E.U`; at each step it takes the pullback of the first old coordinate along
`E.s`. The new last coordinate is obtained from `E.t`. `tupleScheme` and
`tupleProjection` expose this data, and the three projection equations describe
the base case and the appended-coordinate convention.

`tupleProjection_related_first` constructs an arrow from each coordinate to the
first coordinate. It uses the identity section for the base case and the
pullback equation for the appended coordinate. `tupleProjection_related`
uses symmetry and transitivity to relate arbitrary coordinates.

`tuple_hom_ext` proves that maps into a tuple scheme are determined by their
coordinates. Its induction uses the pullback universal property and the
published `EtaleEquivalenceRelation.hom_ext` from
`EtaleEquivalenceRelationGeometry`, which expresses the monomorphism from
`E.R` to `E.U × E.U`. `exists_tuple_lift` proves existence for
every pairwise related family of scheme-valued points, by successive pullback
lifts. Together these give the intended functor-of-points description.

`tupleScheme_isAffine` proves that all these schemes are affine if `E.U` and
`E.R` are affine, using base change of affine morphisms. `tupleProjection_etale`
proves that every coordinate is étale by induction and stability of étale
morphisms under base change and composition.
