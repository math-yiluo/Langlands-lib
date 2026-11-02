# Actual finite presentations by symmetric tuple charts

This is derived infrastructure for the Noetherian first-level proof. Stacks
Project, Decent Algebraic Spaces, Lemma 68.8.6 (Tag 07ST), refers to the
distinct-tuple and symmetric-quotient construction of Lemma 68.8.3 (Tag 0BBN).
The registered sources are `stacks-noetherian-approximation-2026-11-01` and
`stacks-stratification-2026-11-02`. This module assembles the actual finite
family of such charts into a scheme equivalence relation; it does not supply
a Noetherian first level or assert completion of that proof.

`etale_of_finiteEtale_surjective_comp` combines the concrete smooth
source-descent proof with the finite etale source-unramifiedness theorem.
For a finite etale surjection `p : W ⟶ X`, if `p ≫ g` is etale over the
original target `S`, smooth source descent proves that `g : X ⟶ S` is smooth.
The diagonal argument in `FiniteEtaleSourceUnramified` proves formal
unramifiedness of `g`. Smoothness supplies flatness and local finite
presentation, so Mathlib's etale criterion applies. No descent statement is
assumed as a hypothesis. The smooth proof and its helper pairs are carried
unchanged from Worker 293's smooth source-descent implementation, coauthored
with Worker 1224. Its entry module is `SmoothEtaleSourceDescentProof`.
The source-descent mathematics is Stacks, Descent, Lemma 35.14.5 (Tag 05B5),
as explained and sourced in those helper pairs.

`tupleSymmetricCrossLeft_etale` and `tupleSymmetricCrossRight_etale` apply
that criterion to the finite etale surjection from the ordered cross scheme
to the symmetric cross scheme. Each composite endpoint is the ordered
endpoint followed by the symmetric tuple quotient, both etale. These
instances require the original relation's source to be separated and its
object and relation schemes to be affine.

The remaining declarations also assume that the original joint endpoint
map is a closed immersion. `tupleChartRelation length` provides
`FiniteSchemeRelation` data for any family `length : I → ℕ`, where index
`n` denotes tuples with `n+1` entries. Its objects are the symmetric tuple
schemes, and its cross relations are the already constructed symmetric
cross schemes. The closed joint immersion and the etale endpoints are
proved properties of these concrete schemes. The unit, endpoint exchange
and transitivity results supply the three relation laws on points valued
in every scheme.

When `I` is finite, `tupleChartPresentation length` applies
`FiniteSchemeRelation.toEtaleEquivalenceRelation` to that data. Its object
scheme is the coproduct of the charts; its relation scheme is the coproduct
of all ordered pairs of chart cross-correspondences. The three following
instances retain affineness of both schemes and closedness of the joint
endpoint map. The generic assembly proof uses finite extensivity and covers
arbitrary disconnected test schemes.

`tupleChartObjectι` and `tupleChartRelationι` are the canonical component
inclusions. `tupleChartRelationι_t` and `tupleChartRelationι_s` identify
their endpoint composites with the respective symmetric cross endpoint
followed by its object inclusion.

`tupleFinitePresentation N` chooses all indices in `Fin (N+1)`, hence charts
with one through `N+1` entries. `tupleTailPresentation N p` chooses those
indices at least `p`, hence the charts with at least `p+1` entries in that
finite range. Empty tails are permitted. There is no assertion here that
every original relation class meets an arbitrary selected family of charts.
