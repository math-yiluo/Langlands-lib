# Arithmetic model images using canonical local-field integers

Fix a number field `F` in any universe, a finite set `S` of its finite places,
a place `v` outside `S`, and a supplied `IntegralModel` of an actual group
scheme `G` over the ring of `S`-integers. This internal comparison uses the
original finite completion, its topology and its valuation. The canonical
valuation ring is formed using `FiniteCompletion.valuativeRel v`.

`canonicalIntegerMap` is the original inclusion of the `S`-integers into
`v.adicCompletionIntegers F`, followed by the inverse of
`FiniteCompletion.canonicalIntegersEquiv`. The theorem
`canonicalIntegerMap_coe` proves that its value in the completion is the
original inclusion through `F`. This gives the commuting algebra towers
needed by the existing integral-model coefficient extension.

`canonicalModel` applies that coefficient extension to the canonical valuation
ring of the original completion. Its group is the actual scheme pullback
along `canonicalIntegerMap`, as recorded by `canonicalModel_group`.
`isSmooth_canonicalModel` preserves smoothness when the supplied model has it.
`canonicalSubgroup` is its actual integral-section image in the original
`G.affinePoints` coefficient group, using the specified generic isomorphism.

`canonicalSubgroup_eq_subgroup` proves equality of this image with the existing
`IntegralModelCompletions.subgroup`, defined using the original completed
integers. The proof applies the existing original-model coordinate criterion
to both coefficient rings. The identity comparison of canonical and original
integer subrings makes the resulting coordinate-membership tests equivalent.
Thus the statement identifies actual image subgroups and retains the original
generic coefficient maps.

`subgroup_maximal_of_canonicalModel` transfers maximality against every compact
overgroup from the canonical model's rational-point image to that same
arithmetic image. It uses the existing homeomorphic multiplicative comparison
of actual generic rational points and original coefficient points, so the
topologies are the published regular-function evaluation topologies. The
affineness assumption on `G` is explicit.
`subgroup_covering_of_canonicalModel` similarly transfers the literal
parabolic-left product equality for any supplied group morphism `p`.
Both proofs first identify the canonical and original image subgroups and
then apply the existing coefficient-point transport theorems.

These are consequences of the supplied arithmetic model and the previously
proved coefficient and valuation comparisons. The module does not construct a
good reductive or parabolic model, prove local maximality or covering, or prove
the Iwasawa-family existence statement. Its transfer theorems retain the
corresponding local conclusions as explicit premises.
