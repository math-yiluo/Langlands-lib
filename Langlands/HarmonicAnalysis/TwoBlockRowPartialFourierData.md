# The split-row partial Fourier integral (JPSS 1983, Section 4.7)

Module `Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierData`, namespace
`Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier`. Author: Worker 1037.

## Source definition

Jacquet, Piatetski-Shapiro and Shalika, *Rankin--Selberg Convolutions* (1983),
Section 4.7, printed page 413 (PDF page 48, one-based). After the identity (4.7)(1)
on printed page 412, which evaluates `(gΦ)~[ζ_{t_1}, η_{t_2}]` with
`r = t = t_1 + t_2`, the source sets

```text
Φ~(ξ, v) = ∫_{F^{t_1}} Φ[(w, v)] ψ(ξ ᵗw) dw,   ξ, w ∈ F^{t_1}, v ∈ F^{t_2}.
```

The integral transforms the first `t_1` coordinates of a row of length `t_1 + t_2`
with the plus-sign character and holds the last `t_2` coordinates fixed. Over the
commutative field `ξ ᵗw = ∑ i, w i * ξ i = rowPairing w ξ`, and the Lean integrand
`ψ.complex (rowPairing w ξ) * f (join e w v)` is the source integrand with its two
factors in the other order.

Both pages were inspected visually in the registered PDF
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
No errata for this source are registered in the Library or shared notes.

## Hypotheses and conventions

- Block coordinates (`join`, `first`, `second`, `shear`, `contiguousEquiv`) are
  defined for any coefficient type `R`; `joinEquiv` needs `[Semiring R]
  [TopologicalSpace R]`.
- The integral is defined for any `[Field K] [TopologicalSpace K] [MeasurableSpace K]`,
  any `ψ : UnitaryAdditiveCharacter K` and any `μ : AdditiveHaarMeasure K`, and is
  integrated against the Library product measure `rowMeasure μ a`.
- Translation and shear laws add `[IsTopologicalRing K] [BorelSpace K]` and an
  explicit `[SigmaFinite μ.measure]`.
- Schwartz--Bruhat slices, transports and tensors need `[TopologicalSpace K]
  [T2Space K]`. Integrability, the linear map and the expansion formulas additionally
  use `[Field K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [TotallyDisconnectedSpace K]` and `[SigmaFinite μ.measure]`.

Every canonical p-adic field with its Borel structure satisfies these hypotheses.
The source's `dw` is the self-dual measure of Section 0.3 (printed page 378). Here
`μ` is any supplied additive Haar measure: none is chosen or rescaled, and
self-duality is never assumed. The structure `UnitaryAdditiveCharacter` contains
nontriviality, but no construction here uses it. Block sizes `a`, `b` and `N` are
arbitrary naturals, so zero-dimensional blocks are allowed.

## Definitions

For `e : Fin a ⊕ Fin b ≃ Fin N`:

- `join e w v j = Sum.elim w v (e.symm j)`, `first e z i = z (e (Sum.inl i))`,
  `second e z j = z (e (Sum.inr j))`.
- `joinEquiv R e : ((Fin a → R) × (Fin b → R)) ≃L[R] (Fin N → R)` sends `(w, v)`
  to `join e w v`, with inverse `z ↦ (first e z, second e z)`.
- `shear e X z = join e (first e z + Matrix.vecMul (second e z) X) (second e z)`
  for `X : Matrix (Fin b) (Fin a) R`.
- `contiguousEquiv hab = finSumFinEquiv.trans (finCongr hab)` for `hab : a + b = N`.
  It places the first block in the first `a` coordinates and the second block in
  the last `b`. This is the source's row `(w, v)`.
- `firstTranslate e c f z = f (join e (first e z + c) (second e z))`.
- `rowPartialFourierIntegral ψ μ e f ξ v =
  ∫ w, ψ.complex (rowPairing w ξ) * f (join e w v) ∂rowMeasure μ a`, for any
  `f : (Fin N → K) → ℂ`. This is the total Bochner integral, so it is `0` when the
  integrand is not integrable.
- `slice e Φ v : SchwartzBruhat (Fin a → K)` is `w ↦ Φ (join e w v)`.
- `blockTransport e Φ : SchwartzBruhat ((Fin a → K) × (Fin b → K))` is
  `(w, v) ↦ Φ (join e w v)`.
- `joinedTensor e α β : SchwartzBruhat (Fin N → K)` is
  `z ↦ α (first e z) * β (second e z)`.
- `rowPartialFourierTransform ψ μ e :
  SchwartzBruhat (Fin N → K) →ₗ[ℂ] ((Fin a → K) × (Fin b → K) → ℂ)` sends `Φ` to
  `(ξ, v) ↦ rowPartialFourierIntegral ψ μ e Φ ξ v`.
- Instance `rowMeasure_isAddRightInvariant`: `rowMeasure μ d` is right invariant
  under addition. This is Mathlib's instance for `Measure.pi`, transferred to the
  `rowMeasure` name.

The three Schwartz--Bruhat functions are built with the Library's
`SchwartzBruhat.compLeftInverse` and `SchwartzBruhat.tensor`, using the explicit
continuous maps `join`, `first` and `second` as mutual inverses.

## Coordinate laws

- `join_apply`, `first_apply`, `second_apply`, `join_inl`, `join_inr`.
- Inverse laws: `first_join`, `second_join`, `join_first_second`.
- `join_add`, `join_smul`, `continuous_join`, `continuous_first`, `continuous_second`,
  `joinEquiv_apply`, `joinEquiv_symm_apply`.
- Shear: `first_shear`, `second_shear`, `shear_join`
  (`shear e X (join e w v) = join e (w + Matrix.vecMul v X) v`), `shear_zero`,
  `shear_add` (`shear e (X + Y) = shear e X ∘ shear e Y`), `shear_neg_shear` and
  `shear_shear_neg`.
- Contiguous placement: `contiguousEquiv_inl`, `contiguousEquiv_inr` (values
  `Fin.cast hab (Fin.castAdd b i)` and `Fin.cast hab (Fin.natAdd a j)`, the actual
  block inclusions), `first_contiguousEquiv`, `second_contiguousEquiv`,
  `join_contiguousEquiv_castAdd`, `join_contiguousEquiv_natAdd` and
  `join_contiguousEquiv` (`join` is `Fin.append w v` after the cast).

## Pairing

- `rowPairing_add_left`, `rowPairing_neg_left`: linearity in the first variable.
- `rowPairing_join`:
  `rowPairing (join e w v) (join e ξ η) = rowPairing w ξ + rowPairing v η`.
  Proof: reindex the sum by `e` and split it over `Fin a ⊕ Fin b`.
- `complex_rowPairing`: `ψ.complex (rowPairing x y) = ∏ i, ψ.complex (x i * y i)`,
  by induction on the summation set and additivity of the character.

## Integral laws

- `rowPartialFourierIntegral_apply` (the defining formula) and
  `rowPartialFourierIntegral_eq_rowFourierIntegral`: the partial integral equals
  the Library's `rowFourierIntegral ψ μ a (fun w => f (join e w v)) ξ`. Both hold by
  definition.
- `integral_join_add`: for every function `f`, with no integrability hypothesis,
  `∫ w, ψ.complex (rowPairing w ξ) * f (join e (w + c) v) ∂rowMeasure μ a =
  ψ.complex (-rowPairing c ξ) * rowPartialFourierIntegral ψ μ e f ξ v`.
  Proof: Mathlib's `integral_add_right_eq_self` for the right-invariant measure
  `rowMeasure μ a` turns the left side into the integral of
  `ψ.complex (rowPairing (w - c) ξ) * f (join e w v)`. This is an equality of total
  integrals, so it also holds when the integrand is not integrable. Then
  `rowPairing (w - c) ξ = rowPairing w ξ - rowPairing c ξ`, the character is
  additive, and `integral_const_mul` takes out the constant.
- `rowPartialFourierIntegral_firstTranslate`: the translation law
  `rowPartialFourierIntegral ψ μ e (firstTranslate e c f) ξ v =
  ψ.complex (-rowPairing c ξ) * rowPartialFourierIntegral ψ μ e f ξ v`.
  This is `integral_join_add` after `firstTranslate_join`.
- `rowPartialFourierIntegral_comp_shear`: the inverse-phase covariance
  `rowPartialFourierIntegral ψ μ e (f ∘ shear e X) ξ v =
  ψ.complex (-rowPairing (Matrix.vecMul v X) ξ) * rowPartialFourierIntegral ψ μ e f ξ v`.
  This is `integral_join_add` with `c = Matrix.vecMul v X`, after `shear_join`.

## Schwartz--Bruhat laws

- `slice_apply`, `blockTransport_apply`, `joinedTensor_apply`, `joinedTensor_join`
  (`joinedTensor e α β (join e w v) = α w * β v`).
- `exists_joinedTensor_expansion`: every `Φ : SchwartzBruhat (Fin N → K)` equals
  `∑ j, joinedTensor e (α j) (β j)` for finitely many block functions. Proof: apply
  the Library's `SchwartzBruhat.exists_tensor_expansion` to `blockTransport e Φ`
  and evaluate at `(first e z, second e z)`.
- `rowPartialFourierIntegral_eq_rowFourierIntegral_slice`: the partial integral of
  `Φ` is `rowFourierIntegral ψ μ a (slice e Φ v) ξ`.
- `rowPartialFourierIntegral_joinedTensor`: the tensor formula
  `rowPartialFourierIntegral ψ μ e (joinedTensor e α β) ξ v =
  rowFourierIntegral ψ μ a α ξ * β v`, by `joinedTensor_join` and
  `integral_mul_const`.
- `schwartz_rowFourierIntegrand_integrable`: for `f : SchwartzBruhat (Fin d → K)`,
  `w ↦ ψ.complex (rowPairing w ξ) * f w` is integrable for `rowMeasure μ d`. Proof:
  the Library's `rowTensorDecomposition` writes `f` as a finite sum
  `∑ j, c j * ∏ i, g j i (w i)` of products of scalar Schwartz--Bruhat functions.
  With `complex_rowPairing` the integrand becomes a finite sum of products
  `∏ i, ψ.complex (w i * ξ i) * g j i (w i)`. Each factor is integrable by
  `fourierIntegrand_integrable`, each product by Mathlib's
  `Integrable.fintype_prod`, and the sum by `integrable_finsetSum`. This route
  avoids the hypothesis `[BorelSpace (Fin d → K)]` of the Library's
  `rowFourierIntegrand_integrable`.
- `rowPartialFourierIntegrand_integrable`: for every `Φ`, `ξ` and `v`, the integrand
  `w ↦ ψ.complex (rowPairing w ξ) * Φ (join e w v)` is integrable. This is the
  previous result applied to `slice e Φ v`.
- `rowPartialFourierTransform_apply`. The additivity of `rowPartialFourierTransform`
  is `integral_add` for these integrable integrands, and its homogeneity is
  `integral_const_mul`.
- `rowPartialFourierIntegral_sum_joinedTensor`: the partial integral of
  `∑ j, joinedTensor e (α j) (β j)` is `∑ j, rowFourierIntegral ψ μ a (α j) ξ * β j v`.
  This follows from linearity (`map_sum`) and the tensor formula.
- `exists_rowPartialFourierIntegral_expansion`: every `Φ` has a joined-tensor
  expansion, and its partial integral is the corresponding finite sum for all
  `ξ` and `v`.

## Provenance and scope

The definition `rowPartialFourierIntegral` is the source definition on printed
page 413, generalized from the contiguous placement `(w, v)` to an arbitrary
placement `e`. The source row is `join (contiguousEquiv hab) w v`. The other items are
derived internal infrastructure for that definition: coordinate packaging, the
pairing identity, slices, integrability, linearity, joined tensors and the
translation and shear laws. The source does not state these Lean lemmas
separately. On printed page 413 the source integrates over `H_{t_1,t_2}\G_r`, where
`H_{t_1,t_2}` is the lower block-unipotent subgroup of matrices
`[[n_1, 0], [x, n_2]]`. The row shear is only the explicit coordinate map needed for
a later covariance calculation under that subgroup. No subgroup, quotient or
measure on it is constructed here.

This module does not assert that the partial transform of a Schwartz--Bruhat
function is Schwartz--Bruhat, nor any Fourier inversion, comparison with the full
Fourier transform, Mellin identity, functional equation or convergence of the
outer integral over `H_{t_1,t_2}\G_r`. It imports no representation theory.
`Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierShape` identifies the
contiguous placement with the two-block shape of the Rankin--Selberg modules.
