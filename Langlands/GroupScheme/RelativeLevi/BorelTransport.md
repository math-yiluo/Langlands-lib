# Transport of relative Borel subgroups

This internal helper derives transport from the published relative Borel
predicate, reductive residue-field geometry, arbitrary-field geometric Borel
transport and the canonical comparisons for successive pullbacks.

The two `isGeometricBorelSubgroup_*baseChange_comp` lemmas identify Borelness on
an iterated field-valued pullback with Borelness on the pullback along the
composite. They use the natural comparison of pullbacks and transport by source
and ambient isomorphisms.

`IsRelativeBorelSubgroup.comp_iso` and `iso_comp` transport a relative Borel
through ambient and source isomorphisms. Smoothness, affineness and the
monomorphism property transport along the actual scheme isomorphisms; the
residue-field Borel condition transports by the field-level isomorphism lemmas.

`IsRelativeBorelSubgroup.fieldPoint` proves that a relative Borel in a reductive
group becomes geometric Borel on every supplied field-valued fibre. Factor the
given field point through its residue-field fibre, apply arbitrary-field Borel
extension to that connected reductive fibre and compare iterated pullbacks.

`IsRelativeBorelSubgroup.baseChange` preserves the property under arbitrary
scheme base change when the ambient group is reductive. Smoothness, affineness
and the monomorphism property persist; each residue-field point upstairs is a
field-valued point downstairs, so the preceding lemma supplies the geometric
Borel property. A geometric Borel is parabolic in the existing field interface.

`IsRelativeBorelSubgroup.of_baseChange` reflects the property under any flat,
surjective, quasi-compact base change for a supplied closed inclusion into an
affine ambient group. Smoothness descends and source affineness follows from
the closed inclusion. Each downstairs point has an upstairs preimage; the
resulting residue-field extension reflects the geometric Borel property after
the canonical comparisons.

`RelativeBorelData` records an actual Borel presentation and its proof.
`RelativeBorelData.baseChange` pulls back this presentation and uses the
preservation theorem. This module does not assert that a Borel exists.

## Retained sigma-valued pullback

# Relative Borel subgroup transport

This module derives transport properties of the existing relative Borel and
relative parabolic predicates.

Source and ambient group isomorphisms preserve both predicates. For each residue
fibre this follows from the corresponding field-level transport theorem.
Smoothness and affineness of the source and the monomorphism condition are
preserved by the same isomorphisms.

For a reductive ambient group, `IsRelativeBorelSubgroup.fieldPoint` extends the
geometric Borel property from the residue field at the image of a field-valued
point to that point's actual coefficient field. It uses
`IsGeometricBorelSubgroup.baseChange`, the canonical factorization through the
residue field and the natural pullback-composition isomorphisms.

`IsRelativeBorelSubgroup.baseChange` applies this field-point result to each
residue-field point after an arbitrary scheme base change. Pullback stability of
smoothness, affineness and monomorphisms supplies the remaining relative
parabolic conditions. Reductivity of the ambient group is an explicit hypothesis
in these two results.

`relativeBorelBaseChange` packages this operation on actual relative Borel data:
it returns the pullback source, the pullback inclusion and its proved relative
Borel property.

All results are derived from the existing Library predicates, field-extension
theorems and pullback coherence. They do not assert the existence of a Borel
subgroup or of its parameter scheme.

The relative-parabolic source and ambient isomorphism lemmas are imported
from `ParabolicBaseChange`. Their hypotheses and conclusions are shared
unchanged by the relative-Borel transport results.
