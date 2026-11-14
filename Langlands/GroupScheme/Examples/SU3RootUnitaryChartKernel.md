# Special-fibre kernels of diagonal integral unitary chart transitions

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryChartKernel`, namespace
`Langlands.GroupScheme.SU3Root.IntegralChart`.

Let `O` be a commutative local domain, `K` its fraction field, and `L / K` a
separable quadratic field extension, in any universe `u`. Let `C` and `C'` be
integral charts of the actual group `unitaryParameterGroup K L`, indexed by the
same finite type `I`. Write `k = IsLocalRing.ResidueField O` and
`ρ = IsLocalRing.residue O`.

The input `h` is a diagonal change of chart: the two charts have the same
trace-one element, their basis vectors satisfy `e_i = a_i e'_i`, and their
trace-zero central vectors satisfy `f = t f'`, for `a_i, t` in `O` (viewed in
`K`). This is exactly `CoordinateData.IsChartChange` with matrix
`fun i j => algebraMap O K (diagonalMatrix a i j)` and scalar `algebraMap O K t`.
It gives the existing compatible model morphism `C.chartHom C' (diagonalMatrix a) t h`
over the generic identity. The cocycle compatibility is derived from `h`, rather
than assumed as a kernel property.

## Actual residue kernel comparisons

`diagonal_residue_isCompatible` maps the integral cocycle identity along `ρ`.
`diagonalResidueHom` is the resulting actual homomorphism between the two bilinear
coordinate group schemes over `k`, with vector multipliers `ρ(a_i)` and scalar
multiplier `ρ(t)`.

For **every** compatible extension
`φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))`,
`diagonal_specialFibre_square` proves that the canonical residue-coordinate
isomorphisms identify `φ.specialFibreMap` with `diagonalResidueHom`. The proof
uses `IntegralModel.Hom.hom_eq` to identify `φ.hom` with the explicit chart
transition, then uses `BilinearCoordinate.linearHom_baseChange`. Generic rigidity
applies because the actual models are flat and affine over the domain `O`.

`diagonalSpecialFibreKernelIso` applies `kernelSquareIso` to this square. It
identifies the **scheme-theoretic** special-fibre kernel with the kernel of the
reduced diagonal homomorphism. `diagonalSpecialFibreKernelIso_hom_ι` proves that
this isomorphism commutes with the actual kernel inclusions and the residue
source-coordinate isomorphism.

There are two further explicit isomorphisms, obtained by composing with the
diagonal bilinear kernel comparisons:

- `diagonalZeroSpecialFibreKernelIso`, when `ρ(t) = 0`, identifies the kernel
  with the bilinear coordinate group whose vector indices are
  `{i : I // ρ(a_i) = 0}` and whose cocycle is the restriction of
  `fun i j => ρ(C.coeff i j)`. The scalar coordinate remains present.
- `diagonalNonzeroSpecialFibreKernelIso`, when `ρ(t) ≠ 0`, identifies it with
  the polynomial vector group of dimension `Fintype.card {i : I // ρ(a_i) = 0}`.

The underlying diagonal comparisons are natural multiplicative equivalences on
every test scheme, including nonreduced tests. Thus these are isomorphisms of
actual group schemes, rather than calculations only on residue-field points.

## Geometry and alternative presentations

`diagonal_specialFibre_kernel_properties` proves that `kernel φ.specialFibreMap`
is smooth over `k`, connected in its scheme topology, and unipotent in the
Library's representation-theoretic sense. It transports the three established
properties of the reduced diagonal kernel along `diagonalSpecialFibreKernelIso`.
No perfectness or residue-characteristic hypothesis is imposed, and no strict
inequality or nonvanishing condition on the transition coefficients is needed.
In particular the formulas include the cases in which all coefficients reduce
to units or all reduce to zero.

For arbitrary models `M` and `N` of the same generic unitary parameter group,
suppose compatible model isomorphisms
`e : M.Iso C.model (Iso.refl _)` and
`d : N.Iso C'.model (Iso.refl _)` are supplied.
`diagonalPresentationKernelIso` identifies the special-fibre kernel of every
`φ : M.Hom N (𝟙 _)` with the same reduced diagonal kernel.
`diagonal_presentation_kernel_properties` transfers the three properties using
`IntegralModel.Iso.specialFibreKernel_properties`. The comparison isomorphisms
and their compatibility with the generic identity are explicit inputs.

## Provenance and scope

This is a derived application of the actual integral-chart construction and
bilinear diagonal kernel computation to the coordinate law (C.4.2) in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Appendix C.4,
printed pp. 700–702 / PDF pp. 731–733. Lemma C.4.4 proves the corresponding
depth-transition kernel geometry; here the implemented proof first identifies
an arbitrary compatible extension with the chart transition by generic rigidity,
then reduces to diagonal coordinate kernels. The residue-kernel and alternative
presentation isomorphisms are internal supporting constructions.

This module assumes the integral charts, their diagonal change, and any
alternative-presentation isomorphisms. It does not construct valuation-specific
lattice charts, identify them with every supplied root-depth model, perform
restriction-of-scalars assembly, or prove `UnramifiedRootDepthKernelStatement`
(KP Lemma C.5.3). Those comparisons remain separate obligations of Task 6392.
