# Smooth connected affine structure of pseudo-parabolic subgroups

`Langlands.GroupScheme.pseudoParabolicSubgroupStructure` proves the published
`PseudoParabolicSubgroupStructureStatement.{u}`. Over every field `k : Type u`,
for the supplied homomorphism `i : P → G` satisfying
`IsPseudoParabolicSubgroup i`, the structure morphism of `P` is smooth and
affine, and the underlying scheme of `P` is connected. The ambient group is
smooth, connected and affine as in the target. The theorem has no additional
premise.

The new adapter `IsPseudoParabolicSubgroup.source_connectedSpace` proves
connectedness of the same supplied source `P`. It unpacks the existing
presentation into the ground-field unipotent radical `j : U → G`, a
cocharacter `χ`, and the all-test fppf product witness. The explicit group
scheme `Dynamic.Affine.parabolicScheme χ`, with its closed inclusion
`Dynamic.Affine.parabolicHom χ`, represents `Dynamic.parabolic χ`. The
published `dynamicSmooth` proves this representative smooth, and
`dynamicConnected` proves it connected using connectedness of `G`. The
radical is smooth and connected by its existing `IsUnipotentRadical j`
predicate. Both factors are affine because their closed inclusions compose
with the affine structure map of `G`. Closedness of `j` also supplies the
monicity needed for `j` to represent its range.

The published `SubgroupFunctor.IsFppfProduct.connectedSpace` theorem then
applies to these actual representatives. That theorem proves connectedness
of their relative product and descends it through the surjective product
multiplication map onto `P`. In particular, this argument uses the imported
fppf-local product presentation over all relative scheme tests.

The final theorem assembles this adapter with the published
`IsPseudoParabolicSubgroup.source_smooth` and `source_isAffineHom` from
`PseudoParabolicGeometry`. In that module, smoothness descends geometric
reducedness along the epimorphic map from the product of smooth affine
factors, then applies the smoothness theorem for group schemes locally of
finite type over a field. Affineness follows from the closed inclusion of
`P` into affine `G`. This module imports those proofs unchanged.

The provenance of this assembly is the composition of these published
Library results. The target's mathematical provenance remains its stated
derived consequence of Conrad–Gabber–Prasad's dynamic subgroup geometry
and the ground-field radical in the pseudo-parabolic definition. This
proof keeps the target, its imports, and its radical and all-test product
predicates unchanged. It applies in arbitrary universe `u`, including
imperfect and finite fields, and makes no quotient or properness claim.
