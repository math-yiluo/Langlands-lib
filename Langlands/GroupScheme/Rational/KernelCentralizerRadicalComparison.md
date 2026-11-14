# Radicals of full character-kernel centralizer components

This internal construction compares the represented ground-field unipotent
radical of a full character-kernel centralizer identity component with an
ambient kernel. The acting group is a split torus and the character is nonzero;
the full scheme-theoretic kernel is retained, including nonreduced cases.

First, a flat scheme-surjective homomorphism between affine field groups, with
finite-type target and trivial target ground-field radical, kills every
represented source radical. The proof applies the published radical image
containment to the identity section representing the trivial target radical.
It identifies membership in the resulting inverse image of the trivial
subgroup with membership in the actual scheme-theoretic kernel.

For a smooth homomorphism from a smooth affine field group to a connected
reductive group, choose smooth affine representatives of the full
character-kernel centralizers. The target representative is required to be a
closed subgroup. The published centralizer restriction is a smooth scheme
surjection on the actual identity components. The published reductivity
theorem makes its target component connected reductive, so the preceding
kernel containment applies. The ambient commuting square then places the
source component radical in the ambient homomorphism's full kernel on every
scheme test.

If this ambient kernel is represented by a supplied ambient radical,
`kernelCentralizerRadicalMap` is the actual factor homomorphism from the
component radical to the ambient radical. Its composite with the ambient
radical inclusion is exactly the component radical inclusion followed by the
original ambient map. The proved containment also shows that a component
point whose ambient image is outside the ambient radical is outside the
component radical.

The construction has arbitrary common universe and arbitrary ground field.
It assumes neither connectedness of the source ambient group nor connectedness
of the restricted kernel. It proves one-sided containment and does not assert
that the component radical equals the ambient radical intersection. The
supplied radicals are actual representatives satisfying
`IsUnipotentRadical`; no radical existence, quotient existence, residue root
criterion, integral opposite factors, or building theorem is asserted here.

The provenance is internal composition of
`HasSmoothConnectedUnipotentKernel.radical_le_comap`,
`isUnipotentRadical_kernelUnit`,
`kernelCentralizerIdentityMap_smooth_surjective`,
`kernelCentralizerIdentityMap_comp_ambient`,
`kernelCentralizerComponentReductive`, and represented-subgroup
factorization. The first cited theorem does not require any hypothesis on the
kernel despite its namespace. No original-literature claim is added.
