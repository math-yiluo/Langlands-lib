# Renard II.3.13: the right product

Helper module for the proof of
`Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts.Statements`
(Renard, French version of 9 July 2026, II.3.13, printed pp.54–55 /
PDF pp.60–61). The module constructs the product on the existing submodule
`rightEssentiallyCompact μ` and proves the published
`RightProductSpecification`, together with uniqueness. The group and
measure hypotheses are those of the statement: Hausdorff, locally
compact, totally disconnected, Borel, and a left Haar measure.

## Construction

Let `U` be right essentially compact. `rightKernel_hasCompactSupport`
shows that `x ↦ U(y ↦ f(xy))` has compact support. Choose a compact-open
`K` fixing `f` on the right. Then `rightKernel_eq_convolution` identifies
the kernel with the right Hecke convolution `f ⋆ ǩ`, where `kμ = U * e_K`.
Such a `k` exists by `exists_testDensity_eq_right`, and the identification
uses `rightKernel_rightHecke_normalizedIndicator` and
`rightKernel_testDensity`. This is the source's observation that `U * e_K`
lies in the Hecke algebra. The resulting test is `rconv U f`, and
`rconvLinear U` is the corresponding linear map on tests.

`pRDist T U = T ∘ rconvLinear U`, that is `(T*U)(f) = T_x U_y f(xy)`.
`rightHecke_pRDist` proves `(T*U) * h = T * k` whenever `kμ = U * h`.
`rconv_convolution` shows that the left translations in the kernel commute
with the right Hecke convolution. Since `T` is right essentially compact,
`pRDist_mem` follows. `pR` bundles the product as a complex-bilinear map
with `LinearMap.mk₂`.

## Specification

- `pR_assoc`: `rconv_rconv` proves `rconv U (rconv V f) = rconv (pR U V) f`,
  both sides being `x ↦ U_y V_z f(xyz)`. Hence `pR (pR T U) V = pR T (pR U V)`.
- `pR_dirac_left` and `pR_dirac_right`: `dirac 1` is a two-sided unit.
- `pR_compact`: on compactly supported `T` and `U`, `pR` gives the
  published `convolution T U`, by `convolution_apply_rightKernel`.
- `pR_hecke_right`: `pR T (hμ) = T * h`, by `rightKernel_testDensity`.
  `pR_hecke_left`: `pR (hμ) T = h * T`, by `leftHecke_eval`.
- In `pR_spec`, the formula clause turns `f * e_K = f` into right
  `K`-invariance via `rightConvolveTest_eq_iff`. It takes `k` with
  `kμ = U * e_K` and obtains `(T*U)(f) = (T * k)(f)` from
  `rightKernel_eq_convolution`. The last clause is `rightHecke_pRDist`.

Membership of the unit, compact lifts and Hecke lifts in the submodule
comes from `compactlySupported_le_right`.

## Uniqueness

`eq_pR`: for each test `f`, choose a compact-open `K` from
`exists_biInvariant`. The formula clause of any product `p` satisfying the
specification gives `(p T U)(f) = (T * h)(f)`, where `hμ = U * e_K`. The
same kernel identity shows this equals `pR T U f`. Hence `p = pR`.
`right_existsUnique` packages existence and uniqueness.
