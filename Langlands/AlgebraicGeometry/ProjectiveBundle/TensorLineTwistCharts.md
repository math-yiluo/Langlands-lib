# Degree-one chart comparisons for tensor-line invariance

This internal construction uses the published genuine joint frame atlases and
actual tensor-line scheme isomorphism. It constructs local module isomorphisms
on every chart. It does not yet assert that the chart isomorphisms glue.

For a locally free module `M` of rank `n+1` and a locally free rank-one module
`N`, the source comparison is the canonical composite-pullback isomorphism for
`chart ≫ atlasIso.hom`, followed by the source atlas's degree-one chart
isomorphism. The target comparison first uses the proved canonical pullback
tensor comparison, then tensors the tensor atlas's degree-one chart isomorphism
with the actual trivialization of the base line on that chart. The latter uses
the Cartesian chart square, the chosen genuine trivialization of `N`, and the
canonical pullback unit isomorphism. The right tensor unitor gives the standard
relative `O(1)`. Composing the source comparison with the inverse target
comparison gives `TensorFrames.twistChartIso`.

The generic `compHom_local_restrict` lemma derives a restriction formula for
these composite-pullback comparisons from canonical pullback associativity.
This is a derived construction from existing Library definitions and proofs;
no additional geometric or representability assumption is introduced.
