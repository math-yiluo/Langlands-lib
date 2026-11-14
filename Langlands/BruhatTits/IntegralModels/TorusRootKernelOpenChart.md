# Ordered open charts for the full special-fibre kernel

This internal supporting unit composes the full-kernel containment lemma for
Henselian integral models with the actual torus/root factor-kernel comparison.
It uses supplied families `A` and `B` with the same group, building, zero datum
and apartment point, and an identity-generic-fibre model map `ψ : N' → N`.
The finite list `e : Fin n → Option (relativeRoots C.i)` selects the factors
in both ordered charts.

`exists_orderedOpenChartKernel_lift` assumes that the source ordered chart is
an open immersion, that `N'` is smooth, and that every integral section of
`N'` killed by reduction in `N` has its closed point in that chart's range.
The maximal unramified integer ring is Henselian with algebraically closed
residue field. The published `exists_specialFibreKernel_lift` therefore
constructs a morphism from the full scheme-theoretic special-fibre kernel
to the residue pullback of the ordered product. Its composite with the
pulled-back chart is exactly the kernel inclusion.

`orderedOpenChartKernelIso` adds monomorphy of the target ordered chart, the
explicit smooth-homomorphism extension criterion and the pointwise root-depth
inequalities. It chooses the preceding lift and applies
`orderedComparisonKernelIso`, using the monomorphy of the source open
immersion. The result is an isomorphism over the actual residue field from
the finite product of the actual factor kernels to the actual ambient
kernel. This is a scheme isomorphism and asserts no group-law compatibility
with the direct product.

`smooth_connected_kernel_of_orderedOpenCharts` additionally takes the explicit
premise `UnramifiedRootDepthKernelStatement`. The factor-kernel theorem and
the same lift then prove smoothness and connectedness of the full ambient
special-fibre kernel.

The provenance is internal composition of the published Henselian
containment theorem and the torus/root comparison APIs. In particular, this
unit does not construct the supplied families or ordered open charts, prove
the integral-section range condition or root-depth theorem, or claim
unipotence. Those inputs remain obligations of the host proof. The
closed-point condition concerns integral sections whose target reduction is
the identity, rather than only those integral sections whose generic point
is the identity.
