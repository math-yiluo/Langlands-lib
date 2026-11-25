# The analytic premise at a complex place

Module `Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof`. The main results
are in namespace `Langlands.Global.RankinSelbergGlobal`, the helpers in
`Langlands.Global.RankinSelbergGlobal.ComplexPlaceAnalytic`. It is a step towards
`ComplexPlaceFunctionalEquationStatement` (Jacquet 2009, Theorem 2.1, at a complex
place). Provenance: internal.

The module proves the Library premise `ComplexPlaceWhittakerAnalyticStatement` (module
`ComplexPlaceWhittakerBridge`) with no further premise (`complexPlaceWhittakerAnalytic`).
It then states and proves a sharper conditional reduction of the target.

## The reduction statement

```lean
def ComplexPlaceFunctionalEquationLocalReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}
```

In words: the complex-place functional equation follows from four premises:

* the two local functional equations, unequal and equal ranks
  (`ComplexLocalUnequalFunctionalEquationStatement`,
  `ComplexLocalEqualFunctionalEquationStatement`);
* the minus-one premise (`ComplexPlaceMinusOneStatement`);
* the contragredient premise (`ComplexPlaceContragredientParameterStatement`).

All four are Library statements of module `ComplexPlaceFunctionalEquationReduction`. This is a
conditional result, and the four premises stay open here. The theorem
`complexPlaceFunctionalEquationLocalReduction` proves it. It applies the published
`complexPlaceFunctionalEquationAnalyticReduction` and supplies `complexPlaceWhittakerAnalytic`
for the analytic premise.

## The analytic premise

`ComplexPlaceWhittakerAnalyticStatement` covers every standard additive character `χ`, actual
cuspidal realization `T` of `GL_(r+1)`, complex place `w`, finite adelic point `b` and vector
`x`. Write `φ(g) = W_x(ι_w(g) b)` (`cuspWhittaker F T χ x (complexPlacePoint F (r+1) w g *
finitePoint F (r+1) b)`) on `GL_(r+1)(ℂ)`. The statement asserts three things:

* `φ` is smooth;
* `‖φ(g)‖ ≤ C ‖g‖_H^N` for Jacquet's height `complexMatrixHeight`;
* for every complex matrix `X`, the function of `g` given by `W` of
  `T.realization.complexPlaceLieAction w (1 ⊗ X) x` at `ι_w(g) b` is the right derivative
  `Archimedean.rightDerivative (matrixModel ℂ (r+1)) X φ`.

The proof reduces everything to the place-independent results of
`ArchimedeanWhittakerRegularity`, which concern the extended Whittaker function
`archWhittakerExt`.

### Heights (section `Height`)

`complexMatrixHeight g = ∑_(i,j) |g_ij|² + |(g⁻¹)_ij|²` (Jacquet 2009, (2.1)). The module proves:

* `complexMatrixHeight_inv`: `‖g⁻¹‖_H = ‖g‖_H`;
* `complexMatrixHeight_eq_frobenius`: `‖g‖_H = ‖g‖_F² + ‖g⁻¹‖_F²`;
* `two_le_complexMatrixHeight`: `2 ≤ ‖g‖_H`, from `‖g‖_F ‖g⁻¹‖_F ≥ 1`;
* `norm_entry_le_complexMatrixHeight`: `|g_ij| ≤ ‖g‖_H`;
* `norm_det_le_complexMatrixHeight`: `|det g| ≤ n! ‖g‖_H^n`, by the Library's Leibniz bound
  `norm_det_le_factorial_mul_pow`;
* `exists_norm_det_rpow_le_complexMatrixHeight`: for every real `β`,
  `|det g|^β ≤ (n!)^k ‖g‖_H^(n k)` with `k = ⌈|β|⌉`. Both `|det g|` and `|det g|⁻¹` are at most
  `n! ‖g‖_H^n`, and the Library lemma `abs_log_le_log_of_le` turns this into the bound.

These lemmas adapt, from `ℝ` to `ℂ`, the real-place lemmas of the module
`RealMatrixHeightBounds`.

### The determinant norm (section `Determinant`)

`detNorm_complexPlacePoint`: `|det ι_w(g)|_𝔸 = |det g|²`. The infinite idelic absolute value is
`∏_v ‖(det)_v‖^(mult v)`. The component of the determinant is `1` at every place except `w`,
where it is `det g` (`realProjection_det_complexPlaceGL`,
`complexProjection_det_complexPlaceGL`, and the isometries of the completions). Finally
`mult w = 2`. The proof follows `detNorm_realPlacePoint` (module `RealPlaceDeterminantGrowth`).

### Matrix coordinates at `w` (section `Coordinates`)

* `complexPlaceMatrix w A = placeMatrixHom (1, Pi.mulSingle w A)` is the archimedean matrix
  with `A` at `w` and `1` elsewhere.
* `complexDirection w` is the real Lie algebra inclusion at `w` as a continuous real-linear
  map (`realLieAlgebraToMatrix ∘ complexPlaceLieInclusion w`), with
  `complexDirection w B = placeMatrixHom (0, Pi.single w B)` (`complexDirection_apply`).
* `complexPlaceMatrix_eq_add`: `P(A) = P(0) + L(A)`, writing `P = complexPlaceMatrix w` and
  `L = complexDirection w`. So `P` is smooth with derivative `L` everywhere
  (`contDiff_complexPlaceMatrix`, `hasFDerivAt_complexPlaceMatrix`).
* `complexPlaceMatrix_mul_complexDirection`: `P(A) L(B) = L(A B)`, because `placeMatrixHom` is
  multiplicative.
* `complexPlaceGL_val`: the matrix of `complexPlaceGL F n w g` is `P(g)`, so `P` maps invertible
  matrices to invertible ones (`isUnit_complexPlaceMatrix`).

### The three clauses (section `Analytic`)

* `complexPlacePoint_mul_finitePoint`: `ι_w(g) b = (complexPlaceGL w g, b)`, by
  `mul_adelicPoint`.
* `cuspWhittaker_complexPlace`: `φ(g) = archWhittakerExt χ x b (P(g))`, by
  `archWhittakerExt_units`.
* Smoothness (`contMDiff_cuspWhittaker_complexPlace`): `M ↦ archWhittakerExt χ x b (P(M))` is
  `C^∞` on the invertible complex matrices (`contDiffOn_archWhittakerExt` composed with the
  smooth `P`). The Library lemma `Archimedean.contMDiff_of_contDiffOn` then gives smoothness of
  `φ`.
* Growth (`exists_norm_cuspWhittaker_complexPlace_le`): `exists_norm_cuspWhittaker_le` gives
  `‖φ(g)‖ ≤ C |det(ι_w(g) b)|^β = C (|det g|²)^β |det b|^β`. Then
  `exists_norm_det_rpow_le_complexMatrixHeight` with exponent `2β` finishes the bound.
* Lie compatibility (`cuspWhittaker_complexPlaceLieAction`):
  1. By `Archimedean.rightDerivative_eq_fderiv`, `(R(X) φ)(g)` is the derivative at `g`, in the
     direction `g X`, of the extension of `φ` by zero.
  2. That extension agrees near `g` with `M ↦ archWhittakerExt χ x b (P(M))`.
  3. By the chain rule, the derivative is `d archWhittakerExt` at `P(g)` applied to
     `L(g X) = P(g) L(X)`.
  4. By `fderiv_archWhittakerExt_mul`, this is `archWhittakerExt` of `R(L(X)) x` at `P(g)`.
  5. Finally, `R(L(X)) x` is the Lie action of `1 ⊗ X` at `w`, by definition
     (`complexPlaceLieAction_eq_lieDeriv`, which holds by `rfl`).

`complexPlaceWhittakerAnalytic` assembles the three clauses.

## Sources

Jacquet, *Archimedean Rankin–Selberg integrals* (2009), p. 3: the height (2.1) and moderate
growth. The analytic argument (differentiation under the Whittaker integral and the global
`|det|^β` bound) is standard. Here it is carried out from Library results.
