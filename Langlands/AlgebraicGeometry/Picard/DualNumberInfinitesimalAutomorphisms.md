# Actual infinitesimal automorphisms of line bundles

This internal construction combines the published actual dual-number unit
kernel and the published comparison between global units and actual line-bundle
automorphisms. The module and finiteness consequences use the published actual
global-functions module and its proper-case finiteness. It uses no additional
source-specific theorem.

For any scheme over a field, `automorphismReduction` is ordinary pullback of
actual line-bundle automorphisms along the actual zero section.
`InfinitesimalAut` is its kernel, so its elements are actual automorphisms whose
reduction is the identity. There is no chosen trivialization of the line bundle.

`unitKernelAutEquiv` restricts the published scalar equivalence to these kernels.
Its compatibility with reduction follows from ordinary pullback compatibility
of the unit action. `topUnitsEquiv` explicitly identifies units over the
inverse image of the top open with global units; it uses the actual equality
that the inverse image of top is top. `reductionMap_top` identifies the
open-wise map with the zero section's actual map on global sections.

`infinitesimalAutEquiv` combines the kernel restriction with the published
actual unit kernel equivalence: a global function `a` gives scalar
multiplication by the unit `1 + ε a`, with the top-open identification included
in `infinitesimalAutEquiv_val`. The group operation is actual composition of
automorphisms. The commutative law is proved for this existing operation.
`infinitesimalAutAddEquiv` writes this as an additive equivalence with actual
global functions.

The reduction map on automorphisms is surjective for every line bundle on the
thickening. Indeed every reduced scalar unit lifts by the actual projection,
and the scalar comparison respects reduction. No properness, separatedness or
quasi-compactness is used for these assertions.

The scalar action on `Additive (InfinitesimalAut f L)` acts on its unique
global-function coefficient, using the existing field-module structure on
`FieldGlobalFunctions.sections f`. `Function.Injective.module` proves the
module laws while retaining the additive operation just described.
`infinitesimalAutLinearEquiv` is the same coefficient comparison as a linear
equivalence.

The geometric scalar formula is also proved directly.
`pullback_infinitesimalAutEquiv` says that ordinary pullback along the actual
scheme morphism induced by `ε ↦ c ε` sends the coefficient `a` to
`baseSectionMap f ⊤ c * a`. Its target is the automorphism group of the actual
pulled-back line bundle. This follows from pullback compatibility of the scalar
action, the published `scaleSectionMap_coefficientUnit` calculation, and
`scaleSectionMap_top`. The identity `baseSectionMap_top` identifies this
coefficient-field map with the given scheme's `structureRingHom`.

`infinitesimalAutH0LinearEquiv` composes the linear coefficient comparison with
the inverse of the published zeroth-derived-cohomology comparison, obtaining
actual derived structure-sheaf `H⁰`. If `f` is proper,
`finiteDimensional_infinitesimalAut` transfers the published finiteness of
`FieldGlobalFunctions.sections f` along the coefficient equivalence.
These assertions apply over every field and at universe `u`, including empty
schemes, with no chosen trivialization of `L`.

This contribution supplies the actual infinitesimal automorphism calculation
and its module consequences. It does not construct a smooth atlas or an
equivalence of pointed deformation groupoids.
