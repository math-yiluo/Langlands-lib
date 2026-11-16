# Actual geometric lifts of quasi-compact etale morphisms

This internal helper factors out the actual-lift condition in
`EtaleLocalCardinalityFinitenessStatement` and transports it under arbitrary
base change. Its quantifier order agrees exactly with the hypothesis of that
published proposition: the common natural number follows the local ring and
its map to the base, and precedes all algebraically closed field tests and
all their algebra structures.

`pullbackLiftsEquiv` is the pullback universal property on actual morphisms.
Compose a lift with the first projection; the inverse uses `pullback.lift`
with the fixed base point as its second component. The two pullback
projection identities prove the inverse laws. No geometric property of the
maps is required.

`finite_lifts_of_quasiCompact_etale` proves that every actual field-valued
lift type is finite under quasi-compactness and etaleness. The pullback to
the field is locally quasi-finite by the Library etale lemma. Mathlib's
finiteness theorem over a locally Artinian base makes this pullback finite.
The Library theorem on finiteness of sections of a finite morphism over a
field and its equivalence between sections of the fibre and lifts then
give the result. The original morphism is never assumed finite, and this
argument works over every field, without algebraic closedness.

`HasLocalConstantGeometricLiftCardinality.pullback` applies the original
condition to the composite map from a local spectrum. The pullback lift
equivalence identifies each tested cardinality with the original one.
This uses no additional geometric assumptions.

`finrank_eq_closedPoint_of_localRing` proves that a finite flat morphism of
finite presentation over a local spectrum has constant rank. Each prime
specializes to the closed point, and the open rank level set containing
that point must contain every generalization. Applying the Library's
actual-lift rank theorem gives
`natCard_lifts_eq_closedPoint_finrank` for a finite etale morphism and
every algebraically closed field algebra over the local ring.

Provenance: these are internal consequences of the unchanged Library target,
the imported Library finite-section and etale-quasi-finite lemmas, and
Mathlib's pullback and quasi-finite APIs. They are supporting results for
the local-cardinality finiteness proof, and do not assert that finiteness
criterion itself.
