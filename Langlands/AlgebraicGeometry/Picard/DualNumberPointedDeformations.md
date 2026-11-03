# Pointed lifts in the actual dual-number Picard groupoid

This internal construction uses the actual Picard pullback groupoid, its
infinitesimal automorphism calculation, and its ordinary deformation
classes. It invokes no additional source-specific theorem. All schemes
and the arbitrary coefficient field have universe `u`.

For any line bundle `M` on the original field scheme, `PointedDeformations`
is the structured-arrow category from `M` to ordinary zero-section pullback
on the actual Picard groupoids. An object is an actual line bundle `L` on
the dual-number thickening and an actual isomorphism `M ≅ i* L`. Its arrows
are actual bundle isomorphisms commuting with these reduction identifications.
Every arrow is invertible, so this category is a groupoid.

For every pointed object `A`, `pointedAutKernelEquiv` identifies `Aut A`
with the kernel of actual zero-section pullback on automorphisms of the
underlying bundle. The forward map forgets the reduction identification.
The structured-arrow compatibility equation and cancellation of that
identification show that the reduced automorphism is the identity.
Conversely, an actual bundle automorphism in that kernel defines a
compatible pointed automorphism. The inverse laws and preservation of
multiplication retain the actual category operations.

Composing with `infinitesimalAutEquiv` identifies these automorphisms with
the additive group of actual global functions on `X`. In
`pointedAutGlobalFunctionsEquiv_symm_val` the automorphism associated to
`a` is explicitly multiplication by the actual unit `1 + epsilon a`:
the coefficient is pulled back along the thickening projection.
`pointedAutH0AddEquiv` expresses the same comparison with actual derived
structure-sheaf H⁰. Here `Additive` only changes notation for the actual
automorphism composition; no scalar action on `Aut A` is asserted.
These comparisons require no properness or trivialization of the
underlying bundle.

Automorphism reduction is surjective at every `L`. Consequently an arbitrary
isomorphism between the underlying bundles of two pointed objects can be
corrected by an actual automorphism to respect their reduction identifications.
The correction uses the discrepancy between those identifications after the
given isomorphism and a lift of that discrepancy.

The quotient by isomorphisms therefore maps bijectively to ordinary line-bundle
classes whose actual zero-section restriction is the class of `M`.
Surjectivity chooses a reduction isomorphism; injectivity uses the correction
just described. At the trivial bundle this gives `pointedTrivialClassEquiv`
with the actual ordinary deformation kernel already computed by the
`DualNumberDeformationH1`. The class comparison retains the explicit
`pullbackTensorComparisonIsIsoStatement` argument of the ordinary class
construction. The groupoid and automorphism comparisons do not use it.

This unit computes the classes and automorphisms of the actual pointed
dual-number deformation groupoid. It does not construct a smooth chart,
general Artin-ring deformations, or a Rim–Schlessinger equivalence.
