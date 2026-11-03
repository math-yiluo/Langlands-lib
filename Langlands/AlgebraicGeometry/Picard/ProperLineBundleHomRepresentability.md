# Representability of line-bundle Hom on the full scheme slice

Proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.ProperLineBundleHomRepresentabilityStatement`:
for every proper, flat, locally finitely presented morphism of schemes
`f : X ⟶ S`, every scheme `T` over `S` and every two objects `L`, `M` of the
Picard groupoid of the base change `T ×_S X`, the relative Hom presheaf
`CoherentSheaves.intrinsicModuleHomPresheaf ((relativeProjection f).app T) L M`
on `Over T.left` is isomorphic to the functor of points of a scheme `H` over
`T.left` whose structure morphism is affine and locally of finite
presentation.

Theorem: `Langlands.AlgebraicGeometry.Picard.properLineBundleHomRepresentability`.

## Proof as implemented

The theorem is the application of the published reduction
`LineHom.properLineBundleHomRepresentability_of_noetherianModel`
(module `Picard/LineHom/Reduction`, by Worker 633) to
`LineHom.noetherianModel` (module `Picard/LineHom/NoetherianModelProof`), which
proves `LineHom.NoetherianModelStatement`: over a Noetherian affine base, the
Hom presheaf of two locally free sheaves of rank one on a proper flat scheme is,
naturally on the whole slice, the solution presheaf of finitely many
homogeneous linear equations.

The reduction glues over an affine open cover of the base, descends the
proper flat finitely presented geometry and the two line bundles to a
finitely generated, hence Noetherian, ring, applies the Noetherian statement
there, and transports the resulting affine, locally finitely presented
representing scheme back along the base-change isomorphism of the Hom
presheaf. The Noetherian statement is proved by comparing, on affine tests,
the frame coordinates of morphisms of the pulled-back line bundles (gauge
families, `LineHom/FrameHom`, `LineHom/TestCoordinates`) with a two-term
complex of finite projective modules computing the gauge complex after every
base change (`LineHom/CechModel`, `LineHom/GaugeComplex`,
`LineHom/TensorComparison`, `LineHom/SectionsTensor`), whose kernels are
solution sets of a finite linear system (`LineHom/FreeKernel`), and then
extending the comparison from affine tests to the whole slice by the sheaf
property (`LineHom/AffineExtension`).
