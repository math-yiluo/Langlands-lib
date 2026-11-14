# Special-fibre kernels of ramified unitary lattice depth transitions

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryLatticeKernel`, namespace
`Langlands.GroupScheme.SU3Root.IsRamifiedQuadraticValuation`.

Let `O` be a local domain with fraction field `K`, let `L / K` be separable
quadratic, and let `ω` be a ramified quadratic valuation as specified by
`IsRamifiedQuadraticValuation K L ω`. The hypothesis
`hO : IsValuationIntegers O K ω` identifies `O` with the actual nonnegative
valuation subring of `K`. All fields and rings may lie in any universe `u`.

The imported `latticeModel hω hO r s` is the actual smooth affine integral
model `X_{r,s}` of the unitary parameter group. Its integral points are exactly
`X(K)_r · Z(K)_s`, as proved by `mem_integralPoints_latticeModel_iff` in the
model construction. The coordinates use the lattice basis of `Y_r` and the
generator of `Z_{min(s,2r)}`. This module proves the special-fibre kernel
calculation for these constructed models.

## Actual depth-transition comparison

For `r₁ ≤ r₂` and `s₁ ≤ s₂`, the model construction gives the integral change
of chart `isChartChange_transition`. The vector multipliers are powers of the
integral uniformizer with exponents
`⌈r₂⌉ − ⌈r₁⌉` and `⌈r₂ − 1/2⌉ − ⌈r₁ − 1/2⌉`. The scalar multiplier has
exponent
`⌈min(s₂,2r₂) + μ − ω(f)⌉ − ⌈min(s₁,2r₁) + μ − ω(f)⌉`.
The ordered depths make these exponents nonnegative.

`transitionVector` names the vector multipliers.
`transitionMatrix_eq_diagonal` identifies the actual transition matrix with
the diagonal matrix on these multipliers; its proof checks the diagonal and
off-diagonal entries. `isChartChange_diagonal_transition` rewrites the existing
integral change of chart by this matrix identity.

For every
`φ : X_{r₂,s₂}.Hom X_{r₁,s₁} (𝟙 (unitaryParameterGroup K L))`,
`latticeSpecialFibreKernelIso` identifies the actual scheme-theoretic kernel
of `φ.specialFibreMap` with the kernel of `latticeResidueHom`, the diagonal
coordinate transition reduced modulo the maximal ideal.
`latticeSpecialFibreKernelIso_hom_ι` records compatibility with the actual
kernel inclusions. These results apply to every compatible extension, since
the chart comparison uses generic rigidity.

If the scalar multiplier reduces to zero,
`latticeZeroSpecialFibreKernelIso` identifies this kernel with the bilinear
coordinate group on the vector multipliers that reduce to zero, with the scalar
coordinate retained. If the scalar multiplier has nonzero residue,
`latticeNonzeroSpecialFibreKernelIso` identifies the kernel with the polynomial
vector group on those vector indices. Both comparisons concern points over
all residue-field test schemes, including nonreduced tests.

## Kernel geometry and presentations

`lattice_specialFibre_kernel_properties` proves smoothness, connectedness and
representation-theoretic unipotence of the actual special-fibre kernel for
every such `φ`. Its proof applies the chart-kernel theorem to the constructed
lattice charts and the proved diagonal transition. There is no residue
characteristic restriction, and equality in either pair of depths is allowed.

For arbitrary integral models `M,N` of the same generic unitary parameter
group, supplied model isomorphisms over its generic identity from `M` to
`X_{r₂,s₂}` and from `N` to `X_{r₁,s₁}` give `latticePresentationKernelIso`.
`lattice_presentation_kernel_properties` proves the same three properties for
every compatible generic-identity extension from `M` to `N`.

## Provenance and remaining scope

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Appendix C.4,
printed pp. 699–702 / PDF pp. 730–733, constructs `X_{r,s}` using the coordinate
change (C.4.1), the bilinear law (C.4.2), and the lattices `Y_r,Z_s`.
Lemma C.4.4 states the three kernel properties for coordinatewise ordered
depths. The implemented proof uses the actual lattice-chart construction,
the diagonal transition identity, and the all-test bilinear kernel computation.
The explicit residue-kernel isomorphisms and the quantified alternative
presentations are derived supporting constructions.

This module treats the ramified quadratic unitary parameter group with the
specified valuation normalization. It does not identify every supplied
relative root model with a Weil restriction of these models or provide the
remaining root/apartment comparison in `UnramifiedRootDepthKernelStatement`
(KP Lemma C.5.3). Those are separate obligations.
