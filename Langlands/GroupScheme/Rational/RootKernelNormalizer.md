# Kernel centralization and the normalizing torus automorphism

This derived helper connects the all-test centralizer of an actual character
kernel to the torus automorphism of a normalizing point. It applies over an
arbitrary base scheme. The torus homomorphism `i : T.toGrp → G` is only required
to have a monomorphic underlying scheme map. No smoothness, splitness,
primitivity, or nonzero-character condition is imposed.

`normalizerDifference i n` is the torus endomorphism
`id_T - (normalizingAut i n).inv`, using the additive notation for actual
homomorphisms of commutative group schemes.

For `hn : IsNormalizingPoint i n σ` and any character `a`, the theorem
`IsNormalizingPoint.mem_kernelCentralizer_iff` identifies membership of `n`
in `RelativeRoot.kernelCentralizer i a` at the base with the equality
`characterKernelι a ≫ groupHom σ.hom = characterKernelι a`. The proof uses
the actual conjugation formula on every test scheme. Cancellation of the
monomorphism `i` converts commutation into equality on kernel points.
Conversely, equality of these group-scheme morphisms gives the same commutation
formula on every refinement.

`IsNormalizingPoint.characterKernel_comp_inv` applies that equivalence to the
inverse normalizing point. `IsNormalizingPoint.characterKernel_comp_difference`
then proves that the homomorphism `id_T - σ.inv` kills the full character
kernel. Evaluation of subtraction of homomorphisms is division of points;
the two point values agree by the preceding theorem.
`normalizerDifference_kills_characterKernel` specializes this to the chosen
normalizing automorphism and expresses the conclusion as the zero group-scheme
homomorphism, which is the constant identity map on points.

These are internal, derived consequences of the published definitions in
[`RootSubgroup`](RootSubgroup.md) and the conjugation formula in
[`TorusNormalizer`](TorusNormalizer.md). They implement the kernel-triviality
step needed in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), C.2.15 Step 2, printed pp.604–605 (PDF pp.630–631), source ID
`conrad-gabber-prasad-2015-pseudo-reductive`. They do not construct a normalizing
point, assert that it flips a root, or establish intrinsic reflection existence.
The full scheme-theoretic kernel is retained, including any nonsmooth part.
