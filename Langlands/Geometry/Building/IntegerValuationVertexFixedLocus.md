# Global vertex fixed loci from common apartments

This unit extends the apartment vertex-rigidity proof to the whole original
quotient, under the explicit common-apartment premise.

The imported `KPApartmentData.HasCommonApartments` asks that any two points
of the actual quotient be represented in one translate of the actual
apartment. This remains an assumption.
`eq_of_vertex_of_fixed_by_sharpFixer_of_commonApartments` uses the imported
quotient transport lemma to represent a sharp-fixed point in the base
apartment. The imported apartment vertex-rigidity theorem then makes it
the original vertex.

For integer-valued data,
`eq_of_vertex_of_fixed_by_oneStabilizer_of_commonApartments` writes a
vertex as `g • B.apartmentMap a`. Conjugation transports the
one-stabilizer of `a` into that of the given vertex. Hence `g⁻¹ • y`
is fixed by the sharp fixer of `a`. The generic theorem identifies it
with `B.apartmentMap a`, and applying `g` gives `y = x`.

The Prop-valued `VertexFixedLocusFromCommonApartmentsStatement` universally
quantifies this implication over every field `k : Type u`, affine group scheme
`G`, integer-valued valuation `v`, and supplied
`IntegerValuationBuildingData v G`. It assumes common apartments for those
data and concludes that every point fixed by the actual one-stabilizer of
an actual vertex is that vertex. The theorem
`vertexFixedLocusFromCommonApartments` proves this exact conditional
proposition at arbitrary universe `u`.

The imported `MaximalUnramified.CommonApartmentsStatement` states the remaining premise
for the exact fields and supplied building data of Task 6165.
`vertex_fixed_of_commonApartments` derives only the singleton fixed-locus
conclusion from it. No common-apartment existence, boundedness, bounded-subgroup
fixed point or maximality theorem is claimed here. The provenance is internal,
adapting the published local-field `ApartmentFixedPointReduction` directly to
the generic quotient relation.
