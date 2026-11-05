# Local products with the full kernel of an fppf subgroup image

Worker 1150.

This is derived infrastructure for the split-radical product argument. It uses
only the published predicates `SubgroupFunctor.IsFppfImage` and
`SubgroupFunctor.FppfLocallyInProduct`, the actual group-scheme kernel, and
fppf descent for membership in a represented monic subgroup. There is no
external structural theorem or additional field assumption.

`KernelProductFactorization F q x` records an actual test scheme over the base,
a flat, surjective, locally finitely presented projection to the original test,
a left factor in `F`, a right factor whose image under `q` is the identity, and
the ordered factorization after that projection. The noncomputable construction
`IsFppfImage.kernelProductFactorization` chooses this data whenever the image
of `x` belongs to the target subgroup functor `E`. It chooses a representative
of the existential fppf-image data and then uses an actual scheme pullback;
it assumes no local section as input.

For any base scheme `B : Scheme.{u}`, any group-scheme homomorphism `q : G ⟶ Q`,
and subgroup functors `F` and `E` for which `IsFppfImage F E q` holds,
`IsFppfImage.fppfLocallyInProduct_kernel_iff` proves that an arbitrary relative
scheme point `x` belongs fppf-locally to the ordered product of `F` with the
range of `kernelι q` if and only if its image under `q` belongs to `E`.
The kernel is the entire scheme-theoretic kernel, with its points on all
scheme tests. No normality, smoothness, connectedness, affineness, or flatness
of the ambient map `q` is assumed. The actual fppf map between subgroup
representatives comes from `IsFppfImage`.

In the forward direction, apply `q` to the local factorization. The kernel
factor becomes the identity, while `IsFppfImage.map_le` places the other
factor in `E`. Membership descends to the original test by monicity of the
representative of `E` and the fppf effective-epimorphism theorem.

The construction, used in the reverse direction of the equivalence, represents the image of `x` by a point `y` of the
representative of `E`. Pull back the fppf map between the representatives
along `y`, obtaining a flat, surjective, locally finitely presented test map
`a : V ⟶ T` and a lifted point `z` of the representative of `F`. Let `f` be
its image in `G`. The point `f⁻¹ * (a ≫ x)` lies in the full kernel, since
`f` and `a ≫ x` have the same image under `q`. Thus
`a ≫ x = f * (f⁻¹ * (a ≫ x))` is the required ordered local factorization.
No lift over the original test is postulated, and the cover need not be
quasi-compact. This lemma does not construct the subgroup representatives or
prove any particular structural fppf-image assertion.
