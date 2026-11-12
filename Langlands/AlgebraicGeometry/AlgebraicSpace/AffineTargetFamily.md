# Actual families over affine target charts

This internal supporting unit constructs the actual algebraic space over a
target chart V associated to a morphism f of algebraic spaces over S. It first
takes the actual pullback of f along the chart and then applies
`SchemeTargetRebase.space` to its second projection. The construction assumes
no representability of f.

If S and V are affine, quasi-separatedness of the source gives relative
quasi-separatedness of the constructed family. If V is locally of finite
presentation over S, finite-presentation atlas data for source and target,
together with quasi-separatedness of the target, give finite-presentation
atlas data for the family over V. This follows from the existing actual
fibre-product atlas construction and the rebase atlas theorem.

For a surjective etale target chart, the published target-atlas criterion
and the rebase comparison identify geometrically connected nonempty fibres
of f with the same property for the family's structural morphism. When V
is an actual Spec B under the finite-presentation hypotheses above, the
structural component-count criterion identifies this property with every
canonical geometric fibre having exactly one actual connected component.
Nonemptiness remains part of the criterion.

Finally `exists_spec_finitePresentation_atlas` chooses a finite-presentation
affine atlas and replaces its scheme by the spectrum of its global sections.
The affine scheme's canonical isomorphism gives the new map over S; etaleness,
surjectivity and local finite presentation transfer along this isomorphism.

All content is derived from existing Library constructions, their atlas and
fibre comparisons, and affine scheme reconstruction. No external assertion
is introduced. The unit does not prove eventual connectedness along limits
or the full eight-property limit-descent statement.
