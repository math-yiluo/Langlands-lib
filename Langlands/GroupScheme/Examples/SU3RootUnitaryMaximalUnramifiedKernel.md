# Unitary depth-transition kernels over the maximal unramified integers

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryMaximalUnramifiedKernel`,
namespace `Langlands.GroupScheme.SU3Root`.

Let `F` be a nonarchimedean local field and `L` a separable quadratic extension
of its actual maximal unramified field `K = inertiaFixedField F`. The ring of
integers is the actual `O = fixedFieldIntegers F`. Both `F` and `L` lie in an
arbitrary common universe `u`.

The imported `SU3RootUnitaryMaximalUnramified` module constructs the invariant
valuation on `L` and proves its normalized ramification and integer-ring
properties. In particular, this module has no additional valuation,
ramification, residue-field or integer-ring premise.

For arbitrary real depths `r₁ ≤ r₂` and `s₁ ≤ s₂`, consider the constructed
models `Xₖ = maximalUnramifiedModel F L rₖ sₖ`. For every integral-model map
`φ : X₂.Hom X₁ (𝟙 (unitaryParameterGroup K L))`,
`maximalUnramifiedSpecialFibreKernelIso` identifies the actual
scheme-theoretic special-fibre kernel with the kernel of
`maximalUnramifiedResidueHom`. This is the lattice-depth diagonal transition
reduced along the residue homomorphism of `fixedFieldIntegers F`. Its construction
specializes `latticeSpecialFibreKernelIso` to the proved valuation and
integer-ring facts.

`maximalUnramified_specialFibre_kernel_properties` proves that this actual
kernel is smooth, connected and unipotent in the published representation
sense. `maximalUnramifiedTransition_kernel_properties` applies the same result
to the explicitly constructed `maximalUnramifiedTransition`. The proof uses
`lattice_specialFibre_kernel_properties`, whose chart comparison and coordinate
kernel computation hold on all test schemes. Equality in the depths and every
residue characteristic are included.

For arbitrary integral models `M,N` of `unitaryParameterGroup K L`,
`maximalUnramifiedPresentationKernelIso` and
`maximalUnramified_presentation_kernel_properties` give the same comparison and
properties when supplied with integral-model isomorphisms from `M` to `X₂`
and from `N` to `X₁`, both compatible with the generic identity. These
isomorphisms are inputs; the result does not construct them from an equality
of integral-point subgroups.

The provenance is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Appendix C.4, printed pp. 699–702 / PDF pp. 730–733, especially
Lemma C.4.4. The proof specializes the constructed ramified lattice-kernel
calculation to the actual maximal unramified setting of that appendix,
using the imported elementary ramification proof. The explicit residue-kernel
comparison and the compatible-presentation formulation are derived constructions.

This unit concerns the quadratic unitary parameter group over `K`. Restriction
of scalars from other root fields and comparison with arbitrary supplied
relative root and apartment data remain obligations of
`UnramifiedRootDepthKernelStatement` (KP Lemma C.5.3).
