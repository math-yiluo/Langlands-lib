# Integral divisibility from full character-kernel centralization

This derived helper constructs an actual cocharacter by factoring
`id_T - σ⁻¹` through an actual fpqc character `a : T → Gm`, where `σ` is
the torus automorphism of a normalizing rational point. The point is assumed
to centralize the full scheme-theoretic kernel of `a` on every test scheme
and refinement. The underlying map of the torus inclusion is monomorphic.

The construction `normalizerKernelQuotient i n a hc` applies the homomorphism
descent construction in [`HomDescent`](../HomDescent.md). Its kernel-triviality
hypothesis is exactly `normalizerDifference_kills_characterKernel` from
[`RootKernelNormalizer`](RootKernelNormalizer.md). The descent factorization
proves `character_comp_normalizerKernelQuotient`:
`a ≫ normalizerKernelQuotient i n a hc = id_T - σ⁻¹`.
This construction works over an arbitrary base scheme whenever the underlying
character map is quasi-compact, flat, and surjective.

Over a field, `normalizerKernelQuotient_formula` postcomposes that equality
with any character `χ`. The published isomorphism `gmEndEquiv` identifies the
endomorphism `normalizerKernelQuotient ≫ χ` of `Gm` with the integer
`latticePairing T χ normalizerKernelQuotient`. Bilinearity of composition then
gives the whole-character equality
`χ - weylAction i n χ = latticePairing T χ normalizerKernelQuotient • a`.
The inverse in `σ⁻¹` agrees with the published Weyl-action convention.

`exists_integral_difference_of_mem_kernelCentralizer` specializes to a split
torus over any field and any nonzero character. The published
`RelativeRoot.characterFpqc` supplies the three morphism properties without
requiring the character to be primitive. The theorem gives an integer
coefficient for every character difference. The torus need not be maximal,
the ambient group need not be reductive, and the kernel need not be smooth.

This implements the quotient-factorization step in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Theorem C.2.15 Step 2,
printed pp.604–605 (PDF pp.630–631), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`. It is an internal derived
construction from the published actual kernels, normalizer action, fpqc
character theorem, and the homomorphism descent construction authored by
Worker 1335. It assumes a suitable normalizing point; it does not construct
one or prove that it sends a relative root to its negative. Those geometric
inputs are still needed for intrinsic relative-root reflection existence.
