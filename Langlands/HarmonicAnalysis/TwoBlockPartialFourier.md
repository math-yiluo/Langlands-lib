# Two-block partial Fourier identity

Module `Langlands.HarmonicAnalysis.TwoBlockPartialFourier`.

Let `Φ` be a Schwartz–Bruhat function on `N × N` matrices, with the coordinates
split into blocks of sizes `n0` and `n1`. This module proves that integrating the
full Fourier transform of `Φ` over the lower-left block gives the block Fourier
transform of the upper partial integral

```text
Φ^P(A, D) = ∫ B, Φ [[A, B], [0, D]] dB.
```

It is the Library-convention form of Godement–Jacquet, *Zeta Functions of Simple
Algebras* (1972), Lemma 3.4.0, printed page 38. It is used to identify the two
sides of the functional equation for a two-block induced representation. The module
states and proves only this harmonic-analysis fact. It contains no group,
representation or zeta-integral content.

## Conventions

- `K` is any field with the instances `[TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]`. Each lemma uses only the instances it needs.
- `ψ : UnitaryAdditiveCharacter K`. `μ : AdditiveHaarMeasure K` is one scalar
  Haar measure. Every matrix space carries the Library's nested product measure
  `RankinSelberg.rectangularMeasure μ r s`. The module chooses no other
  normalization.
- The full Fourier transform is the Library's raw plus-sign integral
  `rectangularFourierIntegral ψ μ f b = ∫ a, f a * ψ(rectangularPairing a b)`.
  Its pairing is entrywise, `rectangularPairing a b = ∑ i, ∑ j, a i j * b i j`,
  with no transpose. The scalar transform is
  `fourierIntegral ψ μ f y = ∫ x, ψ(x * y) * f x`.
- `IsSelfDual ψ μ` is the Library's scalar self-duality. For every scalar test
  function `f`, the transform `fourierTransform ψ μ f` is integrable against every
  character, and transforming twice gives `x ↦ f (-x)`. The main theorems take
  it as the hypothesis `hsd`. They derive sigma-finiteness of `μ` from it with
  the published `selfDualSigmaFinite`.

Convention difference from the source. Godement–Jacquet pair matrices by the
trace, `τ(x x')`. Under the trace pairing the upper-right block of one matrix pairs
with the lower-left block of the other. Their lemma therefore integrates both
`Φ` and `Φ̂` over the upper-right block. The Library pairing is entrywise, so the
upper-right block pairs with the upper-right block. In this convention the
Fourier side integrates over the lower-left block `C`, which is the radical of
the opposite parabolic. The variables `(x, y)` on the Fourier side pair entrywise
with `(A, D)`.

## Definitions

- `blockMatrix e A B C D : Matrix (Fin N) (Fin N) K`, for
  `e : Fin n0 ⊕ Fin n1 ≃ Fin N`, `A : n0 × n0`, `B : n0 × n1`, `C : n1 × n0`,
  `D : n1 × n1`. Its value is `Matrix.reindex e e (Matrix.fromBlocks A B C D)`,
  the matrix `[[A, B], [C, D]]` in the coordinates `e`.
  `blockMatrix_apply` gives the entry at `(p, q)` as
  `fromBlocks A B C D (e.symm p) (e.symm q)`. The Library's two-block radical
  `RankinSelberg.upperRadical` uses `e = finSumFinEquiv` followed by the cast
  `finCongr (blockRanks_add h)`.
- `entryProductTest g`, for `g : Fin r → Fin s → SchwartzBruhat K`, is the
  Schwartz–Bruhat function `X ↦ ∏ i, ∏ j, g i j (X i j)` on `r × s` matrices.
  It is locally constant as a finite product of locally constant functions. Its
  support lies in the compact product of the scalar supports.
  `entryProductTest_apply` is its evaluation.

## Main results

All results below are for arbitrary `n0 n1 N` and `e`. The ranks may be zero.

- `integral_rectangularFourierIntegral_blockMatrix_lowerLeft` (assumes `hsd`).
  For every `Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) K)`,
  `x : n0 × n0` and `y : n1 × n1`,

  ```text
  ∫ C, rectangularFourierIntegral ψ μ Φ (blockMatrix e x 0 C y) ∂(n1 × n0)
    = ∫ A, ∫ D, (∫ B, Φ (blockMatrix e A B 0 D) ∂(n0 × n1))
          * ψ(rectangularPairing A x) * ψ(rectangularPairing D y) ∂(n1 × n1) ∂(n0 × n0).
  ```

  The right side is the iterated block Fourier integral at `(x, y)` of the upper
  partial integral.
- `integral_rectangularFourierIntegral_blockMatrix_lowerLeft_of_tensor` (assumes
  `hsd`). Let `S` be a finite set, and `Ψ0 k`, `Ψ1 k` Schwartz–Bruhat functions on
  `n0 × n0` and `n1 × n1` matrices. If for all `A` and `D`
  `∫ B, Φ (blockMatrix e A B 0 D) = ∑ k ∈ S, Ψ0 k A * Ψ1 k D`, then for all `x`
  and `y`

  ```text
  ∫ C, rectangularFourierIntegral ψ μ Φ (blockMatrix e x 0 C y)
    = ∑ k ∈ S, rectangularFourierIntegral ψ μ (Ψ0 k) x
                 * rectangularFourierIntegral ψ μ (Ψ1 k) y.
  ```

  So the same tensor data `Ψ0 k`, `Ψ1 k` that expand the partial integral of `Φ`
  also expand the lower-left integral of `Φ̂`, with their block Fourier transforms.
- `integrable_rectangularFourierIntegral_blockMatrix_lowerLeft` (assumes `hsd`).
  The integrand `C ↦ rectangularFourierIntegral ψ μ Φ (blockMatrix e x 0 C y)` is
  integrable for the measure on `n1 × n0` matrices.
- `exists_upperPartialIntegral_tensor` (assumes `[SigmaFinite μ.measure]`). For every
  `Φ` there are `M`, `Ψ0 : Fin M → SchwartzBruhat (n0 × n0)` and
  `Ψ1 : Fin M → SchwartzBruhat (n1 × n1)` with
  `∫ B, Φ (blockMatrix e A B 0 D) = ∑ k, Ψ0 k A * Ψ1 k D` for all `A` and `D`.

## Supporting lemmas

- `prod_blockMatrix`. For any commutative monoid, an entrywise product
  `∏ p, ∏ q, h p q (blockMatrix e A B C D p q)` equals
  `(∏_A · ∏_B) · (∏_C · ∏_D)`. Here `∏_A = ∏ i, ∏ j, h (e (inl i)) (e (inl j)) (A i j)`,
  and similarly for `B` (`inl`, `inr`), `C` (`inr`, `inl`) and `D` (`inr`, `inr`).
- `integral_rectangularMeasure_entryProduct` and
  `integrable_rectangularMeasure_entryProduct` (assume `[SigmaFinite μ.measure]`).
  The integral of `X ↦ ∏ i, ∏ j, f i j (X i j)` is `∏ i, ∏ j, ∫ f i j`. The product
  is integrable when every factor is. Both apply Mathlib's
  `integral_fintype_prod_eq_prod` and `Integrable.fintype_prod` twice, first over
  rows and then over entries. No measurability hypothesis is needed.
- `matrixTensorDecomposition` (assumes only that `K` is a locally compact,
  Hausdorff, totally disconnected space). Every `Φ` on `r × s`
  matrices is `∑ k, c k * ∏ i, ∏ j, g k i j (X i j)` with scalar Schwartz–Bruhat
  `g k i j`. The proof pulls `Φ` back to `Fin (r * s) → K` along
  `finProdFinEquiv`, then applies the published `rowTensorDecomposition`.
- `entryProduct_mul_character`: the kernel identity
  `(∏∏ g i j (a i j)) * ψ(rectangularPairing a b) = ∏∏ ψ(a i j * b i j) * g i j (a i j)`.
- `rectangularFourierIntegral_entryProduct` and
  `integrable_entryProduct_mul_character`. The transform of an entrywise product is
  the entrywise product of scalar transforms `fourierIntegral ψ μ (g i j) (b i j)`,
  and its integrand is integrable for scalar test functions.
- `fourierIntegral_zero`: `fourierIntegral ψ μ f 0 = ∫ f`.
- `rectangularFourierIntegral_const_mul`: scalars pull out of the raw transform.
- `integral_integral_finsetSum_mul`: for integrable `u k` and `v k`,
  `∫ a, ∫ b, ∑ k ∈ S, u k a * v k b = ∑ k ∈ S, (∫ u k) * (∫ v k)`.
- `integral_integral_finsetSum_mul_character`. If every `a k` and `d k`, multiplied
  by its character, is integrable, then the iterated block Fourier integral of
  `∑ k ∈ S, a k A * d k D` is
  `∑ k ∈ S, rectangularFourierIntegral ψ μ (a k) x * rectangularFourierIntegral ψ μ (d k) y`.

## Proof

The proof is by finite tensor decomposition. It does not use a parameter-integral
or tube argument.

1. Write `Φ = ∑ k, c k * T_k` with `T_k X = ∏ p, ∏ q, g k p q (X p q)`
   (`matrixTensorDecomposition`).
2. Fourier side. By linearity and `rectangularFourierIntegral_entryProduct`,
   `Φ̂ Y = ∑ k, c k * ∏ p, ∏ q, ĝ k p q (Y p q)`, where `ĝ = fourierIntegral ψ μ g`.
   At `Y = [[x, 0], [C, y]]`, `prod_blockMatrix` splits each product into four
   block products. The `A` block gives `∏ ĝ(x i j)`. The `B` block is evaluated
   at `0`, and `ĝ(0) = ∫ g` (`fourierIntegral_zero`). The `D` block gives
   `∏ ĝ(y i j)`. Only the `C` block depends on `C`. Its integral is
   `∏ i, ∏ j, ∫ ĝ`, and `∫ ĝ = g 0` by self-duality at `0`. Integrability in `C`
   comes from the integrability of `ĝ`, also supplied by `hsd`.
3. Partial-integral side. At `[[A, B], [0, D]]`, the same splitting shows that
   `∫ B, T_k` is `(∏ g(A i j)) * (∏ ∫ g) * (∏ g 0) * (∏ g(D i j))`, with the
   `B`-block and `C`-block factors as above. So
   `Φ^P(A, D) = ∑ k, (κ k * a_k A) * d_k D`. Here `κ k` collects `c k`, the
   `B`-block integrals and the `C`-block values at `0`, and `a_k`, `d_k` are the
   entrywise products on the diagonal blocks.
4. `integral_integral_finsetSum_mul_character` evaluates the iterated block
   Fourier integral of this sum as `∑ k, κ k * â_k(x) * d̂_k(y)`.
   `rectangularFourierIntegral_entryProduct` turns this into the expression from
   step 2. A ring identity finishes each term.

The tensor form follows by rewriting `Φ^P` with the hypothesis. The integrability
needed is `rectangularFourierEquiv_integrable` for `Ψ0 k` and `Ψ1 k`.
`exists_upperPartialIntegral_tensor` reads step 3 with
`Ψ0 k = κ k • entryProductTest a_k` and `Ψ1 k = entryProductTest d_k`.

## Provenance

This module is derived (internal). The mathematics is Godement–Jacquet 1972,
Lemma 3.4.0 (printed page 38): the Fourier transform of the partial integral
`φ_Φ` is the corresponding partial integral of `Φ̂`. They prove it by the Fourier
inversion theorem in the pair of off-diagonal variables. The statement here is
adapted to the Library's entrywise plus-sign Fourier convention, as explained
under "Conventions". The Lean proof uses finite tensor decompositions and scalar
self-duality, not the two-variable inversion theorem.
