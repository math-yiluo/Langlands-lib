# Renard II.3.13: the left product

Helper module for the proof of
`Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts.Statements`
(Renard, French version of 9 July 2026, II.3.13, printed pp.54–55 /
PDF pp.60–61). This is the mirror image of the right-product module on the
existing submodule `leftEssentiallyCompact μ`. It proves the published
`LeftProductSpecification` and uniqueness under the same hypotheses on the
group and the measure.

## Construction

Let `T` be left essentially compact. `leftKernel_hasCompactSupport` shows
that `y ↦ T(x ↦ f(xy))` has compact support. Choose a compact-open `K`
fixing `f` on the left. Then `leftKernel_eq_convolution` identifies the
kernel with the left Hecke convolution `ǩ ⋆_{μ.inv} f`, where
`kμ = e_K * T`. Such a `k` exists by `exists_testDensity_eq_left`, and the
identification uses `leftKernel_leftHecke_normalizedIndicator` and
`leftKernel_testDensity`. The resulting test is `lconv T f`, with linear map
`lconvLinear T`.

`pLDist T U = U ∘ lconvLinear T`, that is `(T*U)(f) = U_y T_x f(xy)`.
`leftHecke_pLDist` proves `h * (T*U) = k * U` whenever `kμ = h * T`.
`lconv_convolution` shows that the right translations in the kernel commute
with the left Hecke convolution. Hence `pLDist_mem` holds, and `pL` is the
bundled complex-bilinear map.

## Specification and uniqueness

- `pL_assoc` follows from `lconv_lconv`, which proves
  `lconv U (lconv T f) = lconv (pL T U) f`, both sides being
  `z ↦ U_y T_x f(xyz)`.
- `dirac 1` is a two-sided unit.
- On compactly supported `T` and `U`, `pL` gives the published
  `convolution T U` (`convolution_apply_leftKernel`).
- `pL T (hμ) = T * h` follows from `rightHecke_eval`.
  `pL (hμ) T = h * T` follows from `lconv_heckeDistribution`.
- The formula clause converts `e_K * f = f` into left `K`-invariance with
  `leftConvolveTest_eq_iff`. It then obtains `(T*U)(f) = (k * U)(f)` with
  `kμ = e_K * T`.
- The last clause is `leftHecke_pLDist`.

`eq_pL` shows that the formula clause determines every product satisfying
the specification on all tests. `left_existsUnique` packages existence and
uniqueness.
