# Square-zero kernels as actual abelian-group sheaves

This module extends the published `SquareZeroUnitKernels` comparison from
presheaves to sheaves of abelian groups and to actual scheme-morphism kernels.
All declarations are in
`Langlands.AlgebraicGeometry.Picard.SquareZeroUnitKernels`.

For a topological space `X : TopCat.{u}`, let `F` and `G` be presheaves of
commutative rings in universe `u`, with sheaf proofs `hF` and `hG`, and let
`η : F ⟶ G`. The section group of `additiveKernelPresheaf η` on an open
`U` is the actual ideal `RingHom.ker (η.app (op U)).hom`, with its additive
group structure. `additiveKernelPresheaf_isSheaf` proves the sheaf condition:
glue the underlying compatible sections in `F`, use naturality and
separatedness of `G` to show that their gluing maps to zero, and use
uniqueness in `F` for uniqueness in the kernel.
`additiveKernelSheaf η hF hG` bundles this presheaf and proof.

Suppose, in addition, that `h U : SquareZeroKernel (η.app U).hom` for every
opposite open `U`. Thus every product of two elements of each actual
ring-map kernel is zero. The published `kernelPresheafIso η h`, sending
`a` to the unit `1+a`, transfers the sheaf condition to
`unitKernelPresheaf η`. Its section group is the additive notation for the
subgroup of actual units mapped to one by the induced unit-group map.
`unitKernelPresheaf_isSheaf` proves this sheaf condition and
`unitKernelSheaf η hF hG h` bundles it.
`kernelSheafIso η hF hG h` is an isomorphism of abelian-group sheaves,
with the same section maps and inverse as the published presheaf isomorphism.
The inverse sends a unit `u` in the kernel to `u-1`.

For schemes `X Y : Scheme.{u}` and a quasi-compact morphism `i : Y ⟶ X`,
assume `hi : i.ker ^ 2 = ⊥`. Here `i.ker` is Mathlib's ideal-sheaf data,
whose ideals are specified on affine opens. `squareZeroKernel_app i hi U`
proves `SquareZeroKernel (i.app U).hom` for every open `U`, including
nonaffine opens. On an affine neighbourhood `V`, `Scheme.Hom.ker_apply`
identifies the ideal data with `RingHom.ker (i.app V).hom`, and
`IdealSheafData.ideal_pow` identifies its square with the square of that
ideal. Restrict two kernel sections from `U` to `V` using naturality of
`i.c`; the square-zero condition makes their product zero on `V`.
Separatedness of the structure sheaf, applied to these affine
neighbourhoods, then makes the product zero on `U`.

`schemeAdditiveKernelSheaf i` uses the actual structure-map natural
transformation `i.c` from the structure sheaf of `X` to the pushforward
of the structure sheaf of `Y`. `schemeUnitKernelSheaf i hi` uses the
actual units mapped to one by those same section maps. The resulting
`schemeKernelSheafIso i hi` identifies these two abelian-group sheaves
by `a ↦ 1+a`. The source and target are sheaves on the topological
space of `X`; this construction does not identify ideal-sheaf data
itself with an unspecified module sheaf.

The provenance is derived from Oort, *Sur le schéma de Picard* (1962),
§6 Lemma 3 and its proof, printed pp.6–7/PDF pp.7–8 of the retained
15-page scan, registered as `oort-1962-sur-le-schema-de-picard`, SHA-256
`1322c0cfac1bdd6163122345c60f9a57c5778cc23e6091227a4357678c5a2d30`.
Oort identifies a square-zero ideal additively with units congruent to one
and observes restriction compatibility. The generic ring-map kernel
comparison is imported from `SquareZeroUnitKernels`; the sheaf gluing
proof and the bridge from affine ideal data to all actual section kernels
are supplied here using Mathlib's structure maps and affine basis.

No splitting, surjectivity, field, reducedness or closed-immersion
hypothesis is imposed. Quasi-compactness is used for `Scheme.Hom.ker_apply`.
The construction does not classify Picard deformations, prove
surjectivity of unit reduction, provide a cohomology comparison, or
establish representability.
