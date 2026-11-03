# Weight transport through equivariant subgroup representatives

This internal module derives tangent-weight transport directly from the actual
dual-number kernels, coefficient extensions, and all-test equivariance. It uses
no smoothness, splitness, finite-type, or subgroup realization theorem. The
ground field and scheme universe are arbitrary. The source and target group
schemes are affine.

Postcomposition on identity kernels commutes with coefficient extension.
If a group-scheme homomorphism j intertwines the supplied actual torus actions
on every test scheme, its differential maps every intrinsic source weight
space into the corresponding ambient weight space. `actionWeightSpaceMap`
is this linear map with the source and target restricted to those spaces.

If the scheme map j is monomorphic, cancellation shows that the differential
also reflects each all-test eigenvector equation, and its map on weight spaces
is injective. Its image is exactly the intersection of the ambient weight space
and the intrinsic tangent submodule of the range functor. For the reverse
inclusion, the exact tangent-range comparison supplies a source tangent lift,
and weight reflection places that lift in the source weight space.

It follows that a character belongs to the ambient support of the range
precisely when its source weight space is nonzero. For any represented stable
subgroup F, the published `onRepresentedSubgroup` construction supplies the
actual induced action and its equivariance law. The same equivalence then
applies to F. Consequently absence of any character from the ambient support
forces that intrinsic source weight space to be zero. The character can in
particular be zero; this transfers the no-zero-weight hypothesis needed for
structural unipotence and splitness arguments, without proving those structural
results here.

The general identity-kernel target maps and their elementary compatibility
lemmas are reused from `Langlands.GroupScheme.Lie.KernelTargetMaps`. Their
public names and argument conventions are preserved.
