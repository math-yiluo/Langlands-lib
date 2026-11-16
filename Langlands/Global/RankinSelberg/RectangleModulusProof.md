# Proof: the modulus of right multiplication on adelic rectangular matrices

Module `Langlands.Global.RankinSelberg.RectangleModulusProof`. It proves the Library statement
`Langlands.Global.RankinSelbergGlobal.RectangleMeasureModulusStatement` (module
`Langlands.Global.RankinSelberg.RectangleModulusStatement`) with the theorem

```
theorem Langlands.Global.RankinSelbergGlobal.rectangleMeasureModulus :
    RectangleMeasureModulusStatement.{u}
```

It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The statement says this. Let `F` be a number field with `𝔸 / F` compact, let `k, m : ℕ`, and
let `g ∈ GL_m(𝔸)`. Then the image of `rectangleMeasure F k m` on `M_{k×m}(𝔸)` under `x ↦ x g`
is `|det g|_𝔸^{-k} • rectangleMeasure F k m`. In Jacobian form, `d(xg) = |det g|_𝔸^k dx`.

The helper declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RectangleModulus`. The module needs no other new module.

## Provenance

The result is classical. A linear automorphism of `𝔸^n` multiplies Haar measure by the idelic
norm of its determinant (Weil, *Basic Number Theory*, Chapter I §2 locally, then the
restricted product), and right multiplication by `g` acts on each of the `k` rows separately.
The formal proof is internal. It takes the one-row case from the Library and does no local
computation.

## Route

1. **The one-row case is in the Library.** `EqualAnalytic.map_rightMul_rectangleMeasure`
   (module `EqualAnalyticModulus`) says: the image of `rectangleMeasure F 1 m` under
   `rightMul F m g` (`x ↦ x g` on row vectors) is `ENNReal.ofReal (absDet F m g)⁻¹` times
   `rectangleMeasure F 1 m`. This needs `CompactSpace (AdeleQuotient F)`, which the target
   statement assumes.

2. **`rectangleMeasure F k m` is invariant and finite on compact sets.** By definition
   (module `WhittakerIntegrals`), `rectangleMeasure F k m` is the image of the normalized Haar
   measure `normalizedBlockHaarMeasure` of the adelic two-block unipotent group under its
   coordinate map. the imported `rectangleCoordinateHomeomorph F k m` from
   `FourierStandardOutsideProof` packages that coordinate map as a homeomorphism
   onto `M_{k×m}(𝔸)` that turns products into sums (`blockHomeomorph_mul`). The proof is a
   copy, for general `k`, of the Library's `k = 1` argument `rectangleMeasure_isAddHaarMeasure`
   (module `EqualAnalyticRowMeasure`). The normalized measure is a finite scalar
   (`quotientMassNormalizer_ne_top`) times `Measure.haar`, so it is left invariant and finite
   on compact sets. Both properties pass through the homeomorphism: these are the instances
   `rectangleMeasure_isAddLeftInvariant` and `rectangleMeasure_isFiniteMeasureOnCompacts`.
   Neither needs compactness of `𝔸 / F`.

3. **Rows.** `rowsEquiv F k m : M_{k×m}(𝔸) ≃ₜ+ (Fin k → M_{1×m}(𝔸))` sends a matrix to the
   family of its rows. `rowsMeasure F k m` is the product measure
   `Measure.pi fun _ => rectangleMeasure F 1 m`. `productRectangleMeasure F k m` is its image
   under `(rowsEquiv F k m).symm`. A finite product of additive Haar measures is an additive
   Haar measure (Mathlib `Measure.pi.isAddHaarMeasure`), and so is its image under a
   continuous additive equivalence (`ContinuousAddEquiv.isAddHaarMeasure_map`). This gives
   the instance `productRectangleMeasure_isAddHaarMeasure`.

4. **The product measure scales by `|det g|^{-k}`.** `map_rowwise_rowsMeasure` applies
   `rightMul F m g` to every row. By Mathlib `Measure.pi_map_pi`, the image of the product
   measure is the product of the images. Step 1 gives each factor. `pi_const_smul` pulls out
   the constant: a product of `k` copies of `r • ν` is `r ^ k` times the product of copies of
   `ν`. It is proved from `Measure.pi_eq` on boxes. Moving `rightMul` through the row
   splitting (`hcomm`: `(x ↦ x g) ∘ rowsEquiv.symm = rowsEquiv.symm ∘ (rowwise rightMul)`,
   checked entry by entry with `Matrix.mul_apply`) gives the same scaling for
   `productRectangleMeasure F k m`. The constant is rewritten from
   `ENNReal.ofReal (absDet)⁻¹ ^ k` to `ENNReal.ofReal ((absDet ^ k)⁻¹)` with
   `ENNReal.ofReal_pow`, using `absDet_pos`.

5. **Uniqueness of Haar measure.** `rectangleMeasure F k m` is left invariant and finite on
   compact sets (step 2). `productRectangleMeasure F k m` is an additive Haar measure (step 3).
   `M_{k×m}(𝔸)` is locally compact and second countable. Mathlib
   `Measure.isAddLeftInvariant_eq_smul` therefore gives `rectangleMeasure F k m = c •
   productRectangleMeasure F k m` for a constant `c : ℝ≥0`. The image of `c • μ` under the
   measurable map `x ↦ x g` is `c` times the image of `μ` (`Measure.map_smul`). Step 4 and
   commuting the two scalars (`smul_comm`) then give `map_mul_rectangleMeasure`:

   `Measure.map (x ↦ x g) (rectangleMeasure F k m) =
     ENNReal.ofReal ((absDet F m g ^ k)⁻¹) • rectangleMeasure F k m`

   for `g : AdelicGL F m`.

6. **The target.** `rectangleMeasureModulus` applies step 5 to
   `GeneralLinearGroupPoints.adelicEquiv F m g`. The statement's `detNorm F m g` is by
   definition the norm of the determinant of `adelicEquiv F m g`, and this agrees with
   `absDet F m (adelicEquiv F m g)` definitionally, so no rewriting is needed.

## Local instances

As in `WhittakerIntegrals` and `EqualAnalyticRowMeasure`, the matrices
`Matrix (Fin k) (Fin m) (Adeles F)` carry the Borel σ-algebra (`rectModMeasurableSpace`,
`rectModBorelSpace`). The adeles get their Library facts as local instances: Hausdorff
(`EqualAnalytic.t2Space_adeles`), locally compact and second countable. The matrices inherit
local compactness and second countability from `Fin k → Fin m → Adeles F`. The `GL` group
scheme is affine and smooth, and the two-block unipotent subgroup is closed
(`GeneralLinearBlockUnipotent.isClosed_adelicPoints`) and so locally compact. These follow the
Library's `rowGroupClosed` and `rowGroupLocallyCompact`.

## Declarations

- `BlockGroup F k m`, `blockHomeomorph_apply`, `blockHomeomorph_mul` (using
  the imported `rectangleCoordinateHomeomorph`),
  `rectangleMeasure_eq_map_blockHomeomorph` (step 2).
- `normalizedBlockHaarMeasure_isMulLeftInvariant`,
  `normalizedBlockHaarMeasure_isFiniteMeasureOnCompacts`, and the instances
  `rectangleMeasure_isAddLeftInvariant`, `rectangleMeasure_isFiniteMeasureOnCompacts` (step 2).
- `rowsEquiv`, `rowsEquiv_symm_apply`, `rowsMeasure`, `productRectangleMeasure`, the instance
  `productRectangleMeasure_isAddHaarMeasure` (step 3).
- `pi_const_smul`, `map_rowwise_rowsMeasure` (step 4).
- `map_mul_rectangleMeasure` (step 5) and the target theorem `rectangleMeasureModulus`
  (step 6).
