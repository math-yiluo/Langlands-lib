# Smooth homomorphisms restricted to whole-torus centralizers

This internal deduction concerns actual homomorphisms and the full
whole-torus centralizer functors. It uses the published dual-number Lie
construction, the zero-weight description of a torus centralizer, split
weight preimages under a differential, and smoothness from a surjective
actual differential.

For an arbitrary base, postcomposition with `q : G → H` preserves
commutation with the torus on every refinement of every test scheme.
Thus a representative `j : C → G` of the centralizer of `i : T → G`
maps canonically to any representative `l : E → H` of the centralizer
of `i ≫ q`. The constructed `centralizerMap` has ambient composite
`j ≫ q`.

Over any field, assume `T` is split and `G`, `H`, `C` and `E` are smooth
affine group schemes. If `q` is smooth, its actual differential is
surjective. A Lie vector of `E` maps to zero torus weight in `H`.
The split-torus weight-preimage theorem lifts it to zero weight in `G`;
the all-test zero-weight/centralizer equivalence and monicity of `j`
then lift it to the actual Lie module of `C`. Monicity of `l` verifies
that the resulting vector has the prescribed image in `E`.
This proves `centralizerMap_differential_surjective`.
The published square-zero lifting criterion gives
`centralizerMap_smooth`.

The kernel of this smooth restriction is smooth by its actual kernel
pullback. Since `l` is monic, that kernel represents the full kernel of
the original composite `j ≫ q`, so `smooth_kernel_comp` transports
smoothness to the original scheme-theoretic kernel.

No connectedness of the centralizer representatives is required.
The unit does not claim that restriction to a disconnected target
centralizer is surjective.

This is a general supporting construction. Applying it to incident
integral models still requires the actual comparison of their integral
centralizers and compatible product charts. It does not prove the full
ambient incident kernel smoothness or the common-torus statement by itself.
