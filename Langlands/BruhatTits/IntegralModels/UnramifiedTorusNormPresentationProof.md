# A torus norm presentation for the connected integral-point bound

`Langlands.BruhatTits.IntegralModels.unramifiedTorusNormPresentation`
proves the published
`Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationStatement`
at arbitrary universe `u`. The witness is the actual affine Weil restriction
of `T_L` from `L` to `K = inertiaFixedField F`, equipped with its commutative
group structure, and the map is the published algebraic Galois norm.

This proves the norm-presentation prerequisite for the connected-model bound.
It does not construct a smooth integral model or prove surjectivity on neutral
integral points. Those remain separate inputs to the published
`UnramifiedTorusConnectedBoundAssemblyStatement`.

## Provenance

The construction comes from the proof of Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Corollary B.8.7, printed pp. 682–683 / PDF pp. 713–714,
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The statement pair documents its derived existential scope. The 1 November
2024 corrections, registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, do not amend B.8.6–B.8.7.

The tensor-point decomposition adapts the route in the published
`Langlands.GroupScheme.Torus.GaloisNormSmoothnessProof` to construct a group
scheme isomorphism and a group scheme section. The valuation argument uses
the published finite Galois scalar-extension theorem for character-valuation
kernels and the actual evaluation morphism of affine Weil restriction. The
Lean proof below establishes the required inclusion; no equality of bounded
subgroups is needed or asserted.

Worker 323 adapted the complete shared draft of Task 6469 revision 1, authored
by Worker 259 with Worker 302’s input on the prerequisite interface. The
implementation is retained here; this proof is submitted separately against
the published norm-presentation statement.

## Product coordinates over the splitting field

The helpers in `TorusNormPresentation` first work over any finite Galois field
extension `L/k` and any affine commutative group scheme `T/k` whose scalar
extension `T_L` is affine and locally of finite type. These latter hypotheses
follow from `IsSplitTorus T_L` in the final application.

For each `L`-algebra `A`, the finite Galois tensor decomposition identifies
`L ⊗[k] A` with functions from `L →ₐ[k] L` to `A`. The helper
`piAlgebraPointsEquiv` constructs the corresponding equivalence on points
using coordinate-ring homomorphisms. Tensor decomposition and affine
base-change comparison then give a natural multiplicative equivalence
between the `A`-points of the scalar extension of the Weil restriction and
the product of the `A`-points of `T_L` indexed by those embeddings.

`splitProductIso` realizes this natural equivalence as an actual group scheme
isomorphism, using affine point comparison. The equality
`baseChangedNorm_eq_prod` states that the base-changed algebraic norm is
multiplication of these coordinates. Its proof applies tensor evaluation to
`TensorGaloisPoint.extend_norm`, computes evaluation after coefficient
conjugation, and reindexes automorphisms by embeddings.

`source_isTorus` now follows by the product theorem for tori and reflection
of the torus property under field extension. `normSource` retains the same
underlying Weil restriction with its commutative structure, and
`normSource_isAffine` supplies its affine certificate.

## Scheme surjectivity and the full kernel

`normSection` inserts a point into the coordinate of the identity embedding
and puts the unit in every other coordinate. Naturality and affine point
comparison turn this operation into a group scheme morphism over `L`.
The product formula proves `normSection_comp_norm`: its composite with the
base-changed norm is the identity.

`norm_surjective` first deduces scheme surjectivity of the base-changed norm
from this section. The projection from the base-changed target is surjective
because a field extension is faithfully flat. The pullback square then shows
that a composite ending in the original norm is surjective, so the original
norm is itself scheme-surjective.

For `norm_kernel_isTorus`, the product isomorphism makes the base-changed
source a torus. The theorem `Torus.isTorus_kernel_of_section` gives the torus
property of the entire scheme-theoretic kernel of the retraction. Its affine
hypothesis follows by composing the affine kernel inclusion with the affine
source structural morphism. `kernelBaseChangeIso` identifies this kernel
with the scalar extension of the original full kernel, and field-extension
reflection descends the torus property to `k`. The argument concerns the
full pullback kernel, rather than only its identity component or rational
points.

## Character valuations and rational points

`evaluation_extendedCoeff` computes evaluation of a scalar-extended Weil
point on coefficient algebras. `evaluation_of_projected_eq` transfers this
calculation to a base-changed point using its projection to the original
Weil restriction. Applied to `rationalExtend`, these identities prove
`evaluation_rationalExtend`: evaluation after scalar extension of a
`k`-rational Weil point is its inverse image under
`GaloisNorm.rationalPointsEquiv`.

Suppose `vk` extends to `vL` and `vL` is invariant under `Gal(L/k)`. For a
Weil point in `characterValuationKernel vk`, the theorem
`characterValuationKernel_le_comap` puts its scalar extension in the
character-valuation kernel over `L`. The theorem
`map_characterValuationKernel_le` preserves this condition under the actual
evaluation morphism. The evaluation identity therefore shows that the
inverse rational-point comparison is a bounded point of `T_L`.

Finally, `GaloisNorm.norm_rationalPoints` identifies its rational norm with
the image under the algebraic norm. This gives `norm_bounded_image`, the
required inclusion in the norm-defined subgroup `torusNormIwahori`.

## The local-field witness

The final theorem takes `k = inertiaFixedField F`, `vk = fixedFieldValuation F`
and `vL = intermediateValuation F L`. The published valuation-extension
instance and `intermediateValuation_conjugate F L` supply the extension and
Galois-invariance hypotheses. The splitting certificate supplies affineness
and local finite type for `T_L`. Choosing `normSource k L T` and
`GaloisNorm.norm k L T` and applying the preceding results supplies all
conclusions of the unchanged published statement.
