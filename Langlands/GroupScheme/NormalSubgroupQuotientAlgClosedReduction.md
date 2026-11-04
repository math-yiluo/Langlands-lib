# Normal quotients reduce to algebraically closed affine kernels

`AlgClosedNormalSubgroupAffineKernelStatement.{u}` is the construction input:
over every algebraically closed field `k : Type u`, a normal closed subgroup of
a smooth affine group is the full all-test scheme kernel of a homomorphism into
some affine locally finite type group over the same field. This input is
defined here and is not proved here. No smoothness condition is placed on the
normal subgroup.

`NormalSubgroupQuotientAlgClosedReductionStatement.{u}` says that this input
implies the exact published `NormalSubgroupQuotientStatement.{u}` over every
field in the same universe. `normalSubgroupQuotient_of_algClosed_affineKernel`
proves this implication without changing that target or any of its premises.
The conditional reduction retains the original arbitrary characteristic,
imperfect-field and nonsmooth-kernel scope.

The proof base changes `G`, `N` and the original inclusion to `AlgebraicClosure k`
in universe `u`. Smoothness and affineness of `G`, closedness of the inclusion,
and normality of its full subgroup functor persist under base change. The
supplied algebraically closed-field construction yields an actual homomorphism
with the prescribed kernel. `exists_quotient_of_affine_kernel` forms its actual
smooth affine schematic-image quotient. This map is quasi-compact because both
source and target schemes are affine.

The spectrum of the algebraic closure is an affine fpqc cover of `Spec k`.
`Descent.exists_affine_fppfQuotient` therefore descends the quotient group and
map, recovering the exact full range of the original represented subgroup as
kernel. The descended group is affine. Its structure morphism is smooth by
`RelativeRoot.IsFppfQuotient.smooth_target`, applied to the original smooth
source and descended fppf map. These are precisely the original target's
conclusions.

This is derived from the existing base-change, image, affine descent and
smooth-target helpers. The proof uses effective affine descent of the quotient
itself; it does not need coefficients over a finite subextension or a Weil
restriction construction. It remains conditional on the explicitly identified
algebraically closed-field kernel input.
