# Cuspidal support uniqueness from inducing-data rigidity

`Langlands.Global.CuspidalSupportUniquenessReductionStatement.{u, uQ}` is
the implication from `CuspidalInducingDataRigidityStatement.{u, uQ}` to
`CuspidalSupportUniquenessStatement.{u, uQ}`.
`Langlands.Global.cuspidalSupportUniqueness_of_rigidity` proves this
implication. The presentation universe `uQ` is independent of the
number-field and local constituent universe `u`.

## Proof

Fix a finite place and let `ρ` be one of the irreducible local
representations supplied by the constituent predicates. The sum of the
images of intertwiners from `ρ` to the local restriction of `Q` is nonzero
because the predicate supplies an injection. The sum is stable under the
local group by equivariance and under the local centralizer by
postcomposition. The published
`OperatorSubquotient.isJointlyIrreducible_localCentralizerOperators` shows
that the local group and its centralizer act irreducibly together. Their
stability forces the sum to be the whole restriction. The second injection
pulls this isotypic part back to the whole of its source via
`CompactSplitting.isotypicPart_comap_of_injective`. The source is
irreducible, so `CompactSplitting.nonempty_equiv_of_isotypicPart_eq_top`
identifies its isomorphism type with `ρ`.

Take the union of the first witness's spherical exceptional set and the
tensor-exceptional sets of all the presentations on both sides. At a place
outside this union, the chosen reference vectors give nonzero integral
fixed vectors in all inducing components.
`LocalRealization.padicClass_isSpherical_iff` makes their local classes
spherical. The first constituent witness is spherical at this place and
is a subquotient of the first normalized induction. Its equivalence to the
second witness transfers the second subquotient relation by
`Unramified.isSubquotientOf_iff_of_equiv`. The rigidity hypothesis applies
to this common spherical subquotient at every place outside the union. Its
conclusion is the desired bijection matching the positive-rank cuspidal
classes, including repeated classes.

## Provenance

The deduction follows Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 10.7.2 and Corollary 10.7.3, p. 287
(PDF p. 299), registered as `getz-hahn-2024-automorphic-representations`
with SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
Their comparison uses the irreducible unramified subquotients of both
inductions at almost all places. The Library reads the cuspidal input with
the determinant twists absorbed into the realizing representations as on
p. 288 (PDF p. 300).

The supplied rigidity proposition is the finite-place formulation of
Jacquet–Shalika, *On Euler products and the classification of automorphic
forms II* (1981), Theorem (4.4), p. 809 (PDF p. 34), with the definition
of associate pairs on p. 808 (PDF p. 33). The registered source is
`jacquet-shalika-1981-euler-ii`, SHA-256
`4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.

Flath, *Decomposition of representations into tensor products* (1979),
end of the proof of Theorem 1, p. 180 (PDF p. 176), uses isotypy of the
restriction to identify a factor up to isomorphism. Here the embeddings
in the target's hypotheses supply the irreducible representations from
which the proof constructs isotypy directly. The registered source is
`flath-1979-tensor-products`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
