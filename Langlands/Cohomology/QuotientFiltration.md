# Cohomology of successive quotients in a filtration

This is a derived categorical helper for the short exact sequences used in
Stacks Project Lemma 30.21.3, in the registered source
`stacks-noetherian-fibre-section-lifting-2026-11-03`, `02OF.txt`.
It abstracts the elementary quotient and long exact sequence steps, without
asserting the uniform graded vanishing needed by that lemma.

For composable arrows `a : A → B` and `b : B → M` in an abelian category,
`quotientSequence a b` is the canonical sequence
`coker(a) → coker(a ≫ b) → coker(b)`. Its two maps are the induced maps
of cokernels, so `quotientSequence_f` and `quotientSequence_g` specify their
composites with the quotient projections. These equations fix the actual
maps, rather than only identifying their source and target objects.

If `b` is monic, `quotientSequence_shortExact` proves that the sequence is
short exact. The implementation takes the last three terms of Mathlib's
kernel-cokernel sequence for a composition. Exactness is already supplied by
that sequence. The preceding kernel is zero because `b` is monic, giving
monicity of the first quotient map; the final quotient map is epimorphic
because its composite with an epimorphic projection is the projection to
`coker(b)`. Monicity of `a` is not needed.

For an additive left exact functor `F` between abelian categories, with enough
injectives in the source and the chosen derived categories,
`epi_map_quotientSequence_g` proves that `F` sends the final quotient map to
an epimorphism whenever `R¹F(coker(a))` is zero.
`isZero_quotient_middle` proves that vanishing of `RⁱF` on the layer
`coker(a)` and the previous quotient `coker(b)` implies vanishing on the
next quotient `coker(a ≫ b)`. Both results use the published long exact
sequence for actual right-derived functors.

For an ideal-adic filtration, `A`, `B`, and `M` are the successive ideal
multiples and the original module. This file does not construct those ideal
multiples, identify their quotients with a closed fibre, or supply a Serre
vanishing threshold.
