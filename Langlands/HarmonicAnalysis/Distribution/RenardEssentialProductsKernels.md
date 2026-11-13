# Renard II.3.13: kernels of the full Hecke actions

Helper module for the proof of
`Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts.Statements`
(Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, II.3.13, printed pp.54–55 / PDF pp.60–61; source ID
`renard-2026-representations-groupes-reductifs-padiques`). The module
contains internal proof tools only: two scalar kernels and identities for
the published operations. It introduces no new carrier and changes no
published definition.

`G` is a Hausdorff, locally compact, totally disconnected topological group
in an arbitrary universe. In the measure section, `G` has its Borel
structure and `μ` is a left Haar measure. No countability or unimodularity
hypothesis is used.

## Kernels

- `rightKernel U f x = U(leftTranslate x⁻¹ f)`, that is `U(y ↦ f(xy))`
  (`leftTranslate_inv_apply`).
- `leftKernel T f y = T(rightTranslate y f)`, that is `T(x ↦ f(xy))`.

Both are locally constant for every algebraic distribution
(`rightKernel_locallyConstant`, `leftKernel_locallyConstant`). The proofs
rewrite them as the published `leftConvolveTest` and `rightConvolveTest`
composed with inversion. The two kernels are linear in the test
(`rightKernel_linear`, `leftKernel_linear`). `hasCompactSupport_of_vanishing`
gives compact support from vanishing off a compact set.

## Compact-subgroup averages

`rightConvolveTest_compactSubgroupHaar` and
`leftConvolveTest_compactSubgroupHaar` evaluate convolution with the
published `compactSubgroupHaar K` as the published `subgroupIntegral` of
`k ↦ f(xk⁻¹)` and `k ↦ f(k⁻¹x)`. Let `K` be an open subgroup with compact
underlying set. Then `rightConvolveTest_eq_iff` proves `f * e_K = f`
exactly when `f(xk) = f(x)` for all `k ∈ K`. Similarly,
`leftConvolveTest_eq_iff` proves `e_K * f = f` exactly when
`f(kx) = f(x)`. The forward directions use the right- and left-invariance
lemmas `subgroupIntegral_mul_right` and `subgroupIntegral_mul_left`. The
converse directions use `subgroupIntegral_const`.
`exists_biInvariant` takes a compact-open subgroup from the published
`commonCompactOpenBiInvariance` under which a given test is bi-invariant.

`convolution_apply_rightKernel` and `convolution_apply_leftKernel` express
the published compact convolution `convolution T U` as `T` applied to the
right kernel of `U`, or as `U` applied to the left kernel of `T`. They use
`convolution_eq_pairing`, `compactPairing_swap` and
`compactSupportPairing_eq_of_agrees`.

## Identities for a left Haar measure

- `integral_inv_measure`: `∫ g dμ.inv = ∫ g(y⁻¹) dμ(y)`, where `μ.inv` is
  the image of `μ` under inversion.
- `convolution_inversion_apply`: the published right Hecke kernel is
  `(f ⋆ ȟ)(x) = ∫ h(y) f(xy) dμ(y)`, by left invariance.
- `convolution_inv_inversion_apply`: the published left Hecke kernel,
  formed with `μ.inv`, is `∫ h(y) f(yx) dμ(y)`.
- `rightKernel_testDensity` and `leftKernel_testDensity`: the kernels of a
  test density `hμ` are exactly these two Hecke convolutions.
- `rightHecke_eval`: `T(f ⋆ ȟ) = ∫ h(y) · leftKernel T f y dμ(y)`.
  `leftHecke_eval`: `T(ȟ ⋆_{μ.inv} f) = ∫ h(x) · rightKernel T f x dμ(x)`.
  Both apply the published Fubini lemma `distribution_partialIntegral` to
  the published product tests `leftDensityKernel` and `rightDensityKernel`.
- `rightHeckeConvolution_eq_density`: `U * h` is the density of the locally
  constant function `leftConvolveTest U h`, for every distribution `U`.
  This uses Fubini with `leftDensityChangedKernel`.
- `integral_normalizedIndicator_mul`: the published `normalizedIndicator`
  averages to `c` any function equal to `c` on `K`. Consequently,
  `convolution_normalizedIndicator_of_right` and `_of_left` show that the
  Hecke convolutions with `e_K` fix right, respectively left,
  `K`-invariant tests. `rightKernel_rightHecke_normalizedIndicator` and
  `leftKernel_leftHecke_normalizedIndicator` deduce
  `rightKernel (U * e_K) f = rightKernel U f` for right `K`-invariant `f`,
  and `leftKernel (e_K * T) f = leftKernel T f` for left `K`-invariant `f`.
- `leftTranslate_convolution_inversion` and
  `rightTranslate_convolution_inv_inversion` state that translations commute
  with the opposite-side Hecke convolutions.
- `exists_testDensity_eq_right`: if `U` is right essentially compact, then
  `U * h` is the density of a test. `RenardHaar.density_support` makes the
  locally constant density compactly supported.
  `exists_testDensity_eq_left`: if `T` is left essentially compact, then
  `h * T` is compactly supported and invariant under the left action of a
  compact-open subgroup fixing `h` on the left. The left-invariance check
  uses only left invariance of `μ`. The published
  `RenardUniformDensity.left_subset_range` then supplies the test density.
- `convolution_compactTestDensity_apply` and
  `compactTestDensity_convolution_apply`: for compactly supported `T`,
  `T * h` and `h * T` are the published compact convolutions with
  `compactTestDensity μ h`. Hence `compactlySupported_le_right` and
  `compactlySupported_le_left` show that `E′` lies in both essentially
  compact submodules.
