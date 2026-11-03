# Normalizer membership detected on rational points

Worker 1369.

This is an internal derived bridge for the Borel normalizer proof. It proves
no self-normalization theorem and assumes no smoothness or reducedness of a
representing normalizer.

For every base scheme, `SubgroupFunctor.normalizer_carrier_base_le` maps the
base points of the all-test normalizer into the abstract normalizer of the
subgroup of base points. The two implications in abstract normalizer membership
come from conjugation by the point and by its inverse.

Over an algebraically closed field `k : Type u`, let `i : H ⟶ G` be a closed
subgroup with reduced source locally of finite type over `k`.
`range_comp_innerIso_le_of_algClosed_normalizer` proves that every abstract
normalizing point `g` gives the all-test containment
`range (i ≫ (G.innerIso g).hom) ≤ range i`. The implemented proof computes the
image on rational points as conjugation by `g`, uses abstract normalizer
membership, and applies the published
`SubgroupFunctor.range_le_of_algClosed_points`.

Applying that containment to `g` and `g⁻¹` proves
`normalizer_range_carrier_base_eq_algClosed_points`: the base points of the
all-test normalizer are exactly the abstract normalizer of the rational image.
Restriction of a base point to any test scheme is its constant point, so the
two containments supply precisely the two conjugation conditions in the
all-test definition. The ambient group needs no affineness, smoothness or
connectedness assumption.

For an actual Borel embedding `i : B ⟶ G`,
`IsBorelSubgroup.conjugatingIsoOfMemNormalizer` constructs an
isomorphism `φ : B ≅ B` with
`i ≫ (G.innerIso g).hom = φ.hom ≫ i` from abstract normalizer membership.
Borel smoothness gives reducedness by the published smooth-over-a-field
reducedness lemma and supplies local finite type. The all-test containment
factors the conjugated inclusion through `i`; the published Borel transport
lemma turns this factorization into an isomorphism by Borel maximality.
`conjugatingIsoOfMemNormalizer_hom_comp` proves the displayed compatibility
equation for this construction, and
`exists_conjugatingIso_of_mem_normalizer` packages it as an existence theorem.

The provenance is this composition of existing point-containment,
inner-conjugation, represented-subgroup and Borel transport lemmas. These
results justify the rational-point comparison required to use a geometric
Borel-normalizer argument. They do not assert that any such normalizing point
belongs to the Borel.
