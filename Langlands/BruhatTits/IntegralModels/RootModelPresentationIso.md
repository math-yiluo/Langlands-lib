# Root-model presentation isomorphisms

This module develops presentation comparison for the supplied
`RootFiltrationModelData`. It is internal infrastructure for the proof of
`UnramifiedRootDepthKernelStatement`, rather than a proof of the positive
depth kernel geometry in KP Lemma C.5.3.

For an arbitrary domain and fraction field, maps that commute with the
actual all-test root-subgroup inclusions are unique. An inclusion between the
specified ambient filtration subgroups implies preservation of integral
points by such a map: the exact point images give a preimage in the target,
and monomorphy of its root inclusion identifies that preimage with the
image of the given point.

Assuming the explicit smooth homomorphism extension criterion for the base,
equal filtration subgroups therefore give homomorphisms in both directions
between any two supplied smooth models. Generic rigidity makes them inverse,
giving `modelIsoOfFiltrationEq`. The generic representatives can differ.

For two pairs of presentations, the canonical generic identifications
intertwine compatible depth maps by cancellation of the ambient root
inclusion. Generic rigidity gives the corresponding square over the integral
base. Residue base change and `kernelSquareIso` identify the actual
scheme-theoretic kernels. Thus smoothness, connectedness and unipotence of
one special-fibre kernel transfer to the other. No equality of point sets is
used as a replacement for a scheme-theoretic kernel.

Over the actual maximal-unramified integers of a nonarchimedean local field,
`fixedField_hasSmoothHomExtension smoothHomExtension` discharges the extension
criterion using the published arithmetic and the proved strictly Henselian
extension theorem. The resulting `unramifiedModelIsoOfFiltrationEq` has no
unproved proposition premise. The theorem
`unramifiedSpecialFibreKernel_properties_of_presentation` also discharges
that premise for all three kernel properties.

If the two ambient filtration subgroups are equal, generic uniqueness and
generic rigidity identify every supplied depth map with the compatible
model isomorphism. Residue base change preserves this isomorphism. Its
actual kernel is smooth and connected by `KernelIsoGeometry`, and the
second projection of the defining kernel pullback identifies it with the
trivial group scheme. Transport of `isUnipotent_trivial` proves unipotence.
Thus `specialFibreKernel_properties_of_filtration_eq` proves all three
properties, and its unramified specialization has no extension premise.
In particular this covers equality of depths, even with distinct supplied
root representatives and integral models. It also covers unequal depths
whenever their specified filtration subgroups happen to agree.

The model comparison implements the presentation-invariance consequence of
KP Corollaries 2.10.10–2.10.11 and Remark 2.10.19, printed pp.124–127 / PDF
pp.155–158 in the registered 2023 book
`kaletha-prasad-2023-bruhat-tits-new-approach`. The kernel comparison is an
internal consequence of this model comparison and the published pullback
kernel transport. The equal-filtration kernel calculation is an internal
consequence of generic rigidity and the kernel pullback. This module
supplies neither explicit additive/trace-zero/unitary models nor kernel
calculations when the filtration inclusion is strict.
