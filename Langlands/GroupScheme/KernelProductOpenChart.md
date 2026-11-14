# Local product charts for full scheme-theoretic kernels

This is an internal derivation from the published `KernelProductChart`,
finite smooth products, and `smooth_of_nonempty_smoothLocus`. It concerns
the actual scheme-theoretic kernels, including their nonreduced test points.
The cartesian comparison extends the published binary multiplication-cell
construction `SubgroupFunctor.KernelCell` to finite product charts.

Let `q : G → H` be a homomorphism of group schemes over any base `S`, and
let `fᵢ : Aᵢ → Bᵢ` be a finite family of actual factor homomorphisms.
Suppose maps of schemes over `S`,
`m : ∏ Aᵢ → G` and `n : ∏ Bᵢ → H`, satisfy
`m ≫ q = (∏ fᵢ) ≫ n`. The target map `n` must be a monomorphism and take
the product unit section to the unit of `H`. The chart maps need not be
group homomorphisms.

For a point of the source chart killed by `q`, target monicity forces its
image under `∏ fᵢ` to be the unit. Each coordinate lifts through its full
kernel pullback. Taking their product gives `chartKernelLift`; composing
with the product of kernel inclusions recovers the original point.
`isPullback_toKernel` uses these lifts on every test scheme to prove that
the square formed by the product of kernel inclusions, `m`, the full
ambient kernel inclusion and the published `toKernel` is cartesian.
Uniqueness follows from the monomorphisms of the individual kernel
inclusions. No global containment of the ambient kernel in the source
chart is assumed.

Consequently `isOpenImmersion_toKernel` transfers an open-immersion
hypothesis on `m` to this kernel chart by base change.
Over an algebraically closed field, assume also that the full ambient
kernel is locally of finite type and every full factor kernel is smooth.
Their finite product is smooth and has its unit rational point. Its open
chart in the ambient kernel therefore supplies a point of the ambient
smooth locus. Translation in the group scheme propagates the nonempty
smooth locus to all points, by the published
`smooth_of_nonempty_smoothLocus`. This proves
`smooth_kernel_of_openChart`.

This unit does not construct charts for any particular integral model,
prove smoothness of its factor kernels, or assert connectedness of the
ambient kernel. In particular, the common-torus host still requires an
actual compatible target quotient chart and a smooth-kernel argument for
its centralizer factor.
