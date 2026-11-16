# Residue parabolic attainment at every descended facet

This is an internal supporting result for
`UnramifiedFacetParabolicOrderStatement` at arbitrary universe `u`.
`UnramifiedFacetParabolicSurjectivityStatement` retains the complete host
premises: the seven building hypotheses, the eight apartment-descent
hypotheses, the actual unramified zero datum, and a supplied family of models
at every downstairs facet. Each neutral model is smooth and its integral
points after base change to maximal-unramified integers are the intersection
of the zero subgroup with the pointwise fixer of the entire image facet.

For every target facet `Fc`, every supplied reductive quotient `Q` of its
actual neutral special fibre, and every parabolic inclusion `j : H ⟶ Q.quotient`
over the original residue field, the conclusion provides an incident facet
`Fd` whose `Mf.incidentParabolicImage Fc Q Fd` equals `SubgroupFunctor.range j`.
The image uses the actual supplied family comparison, followed by the actual
quotient projection, and is the range of its schematic-image inclusion on
all scheme tests. There is no apartment-point restriction on `Fc`, no extra
source-model existence premise and no residual conjugation in the result.

This is the surjectivity part of the desired order bijection. It does not
assert that the image of every incident facet is parabolic, that the map is
injective, or that the full host proposition holds.

The provenance is internal composition of the actual facet-translation
action, generic rigidity, special-fibre quotient transport, and the direct
apartment-point attainment result in `UnramifiedFacetConjugation`. It makes
no additional translation claim about original literature.

## Implemented proof

`ValuationBuildingData.exists_facetTranslate_apartmentPoint` writes every
actual facet as `g` times the facet containing a point `x` of the distinguished
apartment. The facet's defining translated apartment-facet presentation
contains `g • apartmentMap x`; the apartment axioms identify its containing
building facet, and covariance of `buildingFacetAt` gives the claimed equality.

`FacetModelData.conjugationIso_morphism_square` takes actual compatible
conjugation isomorphisms `α` and `β` on an incident source and its target.
The composite of `α` with the translated family morphism and the composite
of the original family morphism with `β` extend the same generic inner
automorphism. The flat generic rigidity theorem `IntegralModel.Hom.hom_eq`
therefore identifies these actual integral morphisms. This lemma needs no
chosen equivariance or coherence of the supplied family morphisms.

`incidentParabolicImage_translate_transportQuotient` reduces that square to
the special fibre. Transport the quotient on the translated target back
along the inverse residue isomorphism of `β`; its quotient scheme is
literally unchanged and its projection is `β_res.hom ≫ Q.projection`.
After composing the reduced square with `Q.projection`, precomposition by
the residue isomorphism of `α` disappears from the schematic image by
`SchematicImage.range_inclusion_iso_comp`. The translated incident image
thus equals the original incident image for the transported quotient. This
identity works for arbitrary supplied quotient data, without requiring its
reductive-quotient property.

The final theorem `unramifiedFacetParabolicSurjectivity` first writes `Fc`
as a translate of the facet at `x`. The unramified integral-point
characterization and equivariance of `e` give an actual generic-compatible
neutral-model conjugation isomorphism `β` by `exists_neutralConjugationIso`.
Let `Q₀` be `Q` transported back along its residue isomorphism. The theorem
`isReductiveQuotient_transportSpecialFibreIso` proves that `Q₀` is again a
reductive quotient, preserving its actual radical, fppf quotient and
connected reductivity conditions. The same parabolic `j` belongs to its
unchanged quotient scheme.

`unramifiedResidueParabolicAttainment` supplies an incident facet at `x`
whose actual comparison image for `Q₀` is `range j`. Obtain `α` for this
source facet by the same model-conjugation theorem, translate the source
by `g`, and preserve incidence using `facetPrecedes_translate`. The preceding
image-transport identity proves that its actual image for `Q` is `range j`.
All constructions use the supplied downstairs family over the original
integer ring; the maximal-unramified characterization is used to construct
model isomorphisms, rather than replacing the original residue-field image.
