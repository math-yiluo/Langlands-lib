# Smooth connected unipotent kernels over the maximal unramified integers

Module `Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelProof`.

The theorem
`Langlands.BruhatTits.IntegralModels.unramifiedModelKernel` proves the unchanged
published proposition `UnramifiedModelKernelStatement.{u}` at an arbitrary
universe `u`. It has no additional premises.

## Scope

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its maximal
unramified extension and `O = fixedFieldIntegers F` its integers. The target
supplies an affine group `G` over `F`, connected reductive building data `C`
for `G_K`, an arbitrary zero datum `E`, a common translate `g` of the apartment,
and apartment subsets `Ω` and `Ω'`. It assumes that `Ω` is nonempty, that every
real affine functional is bounded above on `Ω'`, and that `Ω` lies in the
closure of `Ω'` for the topology induced by those functionals.

For any smooth integral models `N` and `N'` with the specified integral points
`E.zeroPoints` intersected with the pointwise fixers of `g • Ω` and `g • Ω'`,
and every `ψ : N'.Hom N (𝟙 _)`, the full scheme-theoretic kernel of
`ψ.specialFibreMap` is smooth, has connected underlying space, and is unipotent
over the residue field of `O`.

Model existence and existence of building data are outside this statement.
The theorem proves all three kernel properties for every presentation covered
by the existing target. It adds no connected-fibre assumption or compatibility
condition on the supplied zero datum.

## Implemented proof

The proof first applies `unramifiedModelKernel_of_smoothConnected`, from
`UnramifiedModelKernelTorus`. Its two global premises are discharged by

```lean
unramifiedQuasiSplit_of_henselianDiscrete
  (henselianDiscreteQuasiSplitReduction
    (quasiSplitRegularClassRationalReduction quasiSplitSteinbergQuotient))
```

and `unramifiedZeroPointsIndependence`. This reduction handles the common
translation, chooses zero data whose torus represents the centralizer of the
building's maximal split torus, compares the zero subgroups, and supplies
unipotence once smoothness and connectedness are proved. Its torus argument
uses bounded split-torus points in both models and injectivity on special
fibres. The remaining goal is the compatible apartment version asserting
smoothness and connectedness.

For that goal, the proof proceeds as follows.

1. The affine-closure hypotheses imply that `Ω'` is nonempty and every real
   affine functional is bounded above on `Ω`. Choose `x ∈ Ω` as a common
   apartment reference point.
2. The private helper `commonOrderedRootData` chooses one generic cocharacter
   and finite injective enumerations of the indivisible roots of its two
   signs. It uses `exists_genericCocharacter`,
   `finite_relativeRoots` and
   `exists_fin_enumeration_indivisiblePositiveRoots`, lifting the latter's
   character-valued lists to the actual root subtype. The order is negative
   indivisible roots, one torus slot, positive indivisible roots. Either root
   list may be empty; doubled roots are not separate slots.
3. Apply the proved `unramifiedOrderedIntegralOpenCell` to `N` and `N'`,
   using the same `x`, generic cocharacter and root lists. This constructs
   actual torus/root model families `A` and `B` with open ordered integral
   multiplication maps. The target chart is consequently monomorphic.
4. The proved `unramifiedOrderedFixerFactorization` supplies ordered
   factorization for the two fixer subgroups. The lemma
   `A.closedPoint_mem_range_orderedChart` then places the closed point of
   every integral section of `N'` killed by reduction in `N` in the source
   ordered chart.
5. The affine-closure hypothesis gives the depth inequalities
   `rootFixerDepth a x Ω ≤ rootFixerDepth a x Ω'` for every relative root.
   The smooth extension property over the actual ring `O` is
   `IntegralModel.fixedField_hasSmoothHomExtension
   IntegralModel.smoothHomExtension F`.
6. Apply `A.smooth_connected_kernel_of_orderedOpenCharts` with those
   inequalities, the extension property, the closed-point range condition,
   and the proved `unramifiedRootDepthKernel`. The chart theorem uses
   Henselian lifting and the algebraically closed residue field to place
   the full kernel scheme in the open cell. It identifies that scheme with
   a finite product of the actual torus/root comparison kernels. The torus
   comparison is invertible and the root-depth theorem gives smoothness and
   connectedness of the root kernels, so the ambient kernel is smooth and
   connected.

The product comparison in the last step is an isomorphism of schemes over the
residue field. The proof obtains unipotence from the separate torus reduction
in the first step; it does not require the product comparison to preserve a
direct-product group law.

Every proposition supplied to these reductions is proved by an imported
Library theorem. In particular, the proof uses neither
`UnramifiedParahoricModelStatement` nor an unproved open-cell, root-depth,
factorization, quasi-splitness or independence statement as an extra premise.
The only new auxiliary content is the private common root enumeration and an
affineness instance for the base-changed group.

## Provenance

The mathematical target is the kernel assertion of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 8.4.15, printed
pp. 306–307 / PDF pp. 337–338, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered `kaletha-prasad-2024-corrections`, PDF pp. 37–38, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
adds the perfect-residue assumption and specifies the integral-model map
whose base change is the special-fibre map. The nonarchimedean local field
setting and the supplied model map in the published target incorporate this
setup.

The implemented route follows the source's ordered open cell and root-kernel
argument using published internal comparison and transport lemmas. The
unipotence argument uses the published torus reduction. The target's paired
Markdown explains its arbitrary-presentation, arbitrary-zero-datum and common
translation formulation. This module leaves that statement and its imports
unchanged and proves only its three kernel properties; the product
isomorphism assertion of Proposition 8.4.15 is not part of the target.
