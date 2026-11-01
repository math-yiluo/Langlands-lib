# Commutation of the chosen full and partial rectangular Fourier transforms: proof

Worker 1167 wrote this module for task `f80c9a8a-60b6-4ac7-b243-0426fc520944`.
`Langlands.HarmonicAnalysis.rectangularFourierCommutation.{uK}` proves exactly
the closed published proposition
[`RectangularFourierCommutationStatement`](RectangularFourierCommutationStatement.md).
The proof keeps the implicit carrier `K : Type uK`, all eight typeclass
hypotheses on it, every unitary additive character `ψ`, every supplied
additive Haar measure `μ`, every rank `n : ℕ`, the sole premise
`hsd : IsSelfDual ψ μ`, and every
`Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)`. It proves the equality
of Schwartz–Bruhat functions

```text
rectangularFourierEquiv ψ μ n (n + 1) hsd (partialFourierEquiv ψ μ n hsd Φ) =
  partialFourierEquiv ψ μ n hsd (rectangularFourierEquiv ψ μ n (n + 1) hsd Φ).
```

Write `F = rectangularFourierEquiv ψ μ n (n + 1) hsd` and
`T = partialFourierEquiv ψ μ n hsd`. The target pair and every pair it
imports are used unchanged.

## Route

The proof does not split `RankinSelberg.rectangularMeasure μ n (n + 1)` into a
first-block measure and `rowMeasure μ n`, and it exchanges no iterated
integrals of general integrands. The task contract allows another route that
proves the exact target. This proof uses finite tensor decomposition instead.

1. Every test `Φ` is a finite complex linear combination of entrywise products
   `X ↦ ∏ i, ∏ j, g i j (X i j)` of scalar tests `g i j : SchwartzBruhat K`.
2. `F` and `T` are complex-linear, so it suffices to prove the identity for one
   entrywise product.
3. For an entrywise product, both `F` and `T` give entrywise products of
   explicit scalar functions. Each integral that occurs is the integral of a
   product of one-coordinate functions against a finite product measure
   `Measure.pi`. This is evaluated with `integral_fintype_prod_eq_prod`.
4. The two resulting products agree factor by factor. In the last column,
   negation invariance of the regular additive Haar measure `μ.measure`
   identifies the two remaining scalar integrals.

The proof uses no Fourier inversion. Self-duality enters only as the argument
the two chosen maps require, and to derive sigma-finiteness of `μ.measure`.

## Imported results

All of the following are published results, imported by Lean name.

- From [`TwoBlockPartialFourier`](TwoBlockPartialFourier.md):
  - `entryProductTest g` is the Schwartz–Bruhat function
    `X ↦ ∏ i, ∏ j, g i j (X i j)`, with `entryProductTest_apply`.
  - `matrixTensorDecomposition Φ` writes every rectangular test as
    `Φ X = ∑ k, c k * ∏ i, ∏ j, g k i j (X i j)`.
  - `rectangularFourierIntegral_entryProduct`, under `SigmaFinite μ.measure`,
    states that the raw full integral of an entrywise product of *arbitrary*
    scalar functions is `∏ i, ∏ j, fourierIntegral ψ μ (g i j) (b i j)`. It
    applies `integral_fintype_prod_eq_prod` twice to the actual nested product
    `Measure.pi (fun _ => Measure.pi (fun _ => μ.measure))`.
- From [`SelfDualSigmaFiniteProof`](SelfDualSigmaFiniteProof.md):
  `selfDualSigmaFinite` derives `SigmaFinite μ.measure` from `IsSelfDual ψ μ`
  under the same generic field hypotheses.
- From [`RectangularFourierEquiv`](RectangularFourierEquiv.md) and
  [`PartialFourierEquiv`](PartialFourierEquiv.md): the evaluation lemmas
  `rectangularFourierEquiv_apply` and `partialFourierEquiv_apply`. These
  identify the chosen maps with the raw integrals `rectangularFourierIntegral`
  and `partialFourierIntegral`.
- From Mathlib: the instance `IsAddHaarMeasure.isNegInvariant_of_regular`
  (a regular additive Haar measure on a locally compact abelian topological
  group is invariant under negation), `integral_neg_eq_self`,
  `integral_const_mul`, `integral_fintype_prod_eq_prod` and
  `Fin.prod_univ_castSucc`.

## Declarations in this module

### `fourierIntegral_comp_neg`

For every function `G : K → ℂ` and every `z : K`,

```text
fourierIntegral ψ μ (fun t => G (-t)) z = fourierIntegral ψ μ G (-z).
```

The hypotheses are the field, topological-ring, Borel and local-compactness
instances. `μ.measure` is an additive Haar measure. It is regular by the
`regular` field of `AdditiveHaarMeasure`, so the Mathlib instance makes it
negation invariant. The proof rewrites the left integral
`∫ x, ψ.complex (x * z) * G (-x)` by `integral_neg_eq_self`. The result is
`∫ x, ψ.complex (-x * z) * G x`, and `-x * z = x * -z`. No integrability is
needed: `integral_neg_eq_self` holds for every function.

### Reused `complex_finsetSum`

The complex character of a finite sum is the product of the complex
characters of the summands. This proof reuses the public helper in
[TwoBlockPartialFourier](TwoBlockPartialFourier.md), proved by finite induction
with `AddChar.map_add_eq_mul`.

### `partialFourierIntegral_entryProduct`

Assume `SigmaFinite μ.measure`. For *arbitrary* scalar functions
`g : Fin n → Fin (n + 1) → K → ℂ` and every `m`,

```text
partialFourierIntegral ψ μ (fun a => ∏ i, ∏ j, g i j (a i j)) m =
  ∏ i, ((∏ k : Fin n, g i k.castSucc (m i k.castSucc)) *
    fourierIntegral ψ μ (g i (Fin.last n)) (-m i (Fin.last n))).
```

Unfold `partialFourierIntegral` and write `x = rectangularFirstColumns m`.
For each `u`, the integrand
`(∏ i, ∏ j, g i j (rectangularJoin x u i j)) * ψ.complex (-rowPairing (rectangularLastColumn m) u)`
is rewritten pointwise into two factors. The first factor is the constant
`∏ i, ∏ k, g i k.castSucc (m i k.castSucc)`, obtained with
`Fin.prod_univ_castSucc`, `rectangularJoin_castSucc` and
`rectangularJoin_last`. The second factor is the product
`∏ i, ψ.complex (u i * -m i (Fin.last n)) * g i (Fin.last n) (u i)`. To get
it, the negated row pairing is the sum `∑ i, -(m i (Fin.last n) * u i)`, and
`complex_finsetSum` turns its character into a product. The constant leaves
the integral by `integral_const_mul`. Here `rowMeasure μ n` is by definition
`Measure.pi (fun _ : Fin n => μ.measure)`. `integral_fintype_prod_eq_prod`
then evaluates the remaining integral as
`∏ i, ∫ t, ψ.complex (t * -m i (Fin.last n)) * g i (Fin.last n) t ∂μ.measure`.
Each factor is `fourierIntegral ψ μ (g i (Fin.last n)) (-m i (Fin.last n))` by
definition. Merging the two products with `Finset.prod_mul_distrib` gives the
stated form. Both product-integral lemmas hold for arbitrary functions once
the factor measures are sigma-finite, so no integrability or measurability
argument appears.

### `rectangularFourierCommutation_entryProduct`

Under the full telescope and `hsd`, for every
`g : Fin n → Fin (n + 1) → SchwartzBruhat K`,

```text
F (T (entryProductTest g)) = T (F (entryProductTest g)).
```

The proof first installs `SigmaFinite μ.measure` from
`selfDualSigmaFinite K ψ μ hsd`. Then:

- **`T` of the product.** Define scalar functions `g' i j` by `Fin.lastCases`:
  `g' i (Fin.last n) = fun t => fourierIntegral ψ μ (g i (Fin.last n)) (-t)`,
  and `g' i k.castSucc = g i k.castSucc`. By `partialFourierEquiv_apply` and
  `partialFourierIntegral_entryProduct`, the function underlying
  `T (entryProductTest g)` is `a ↦ ∏ i, ∏ j, g' i j (a i j)`. Splitting
  `∏ j` with `Fin.prod_univ_castSucc` matches the two forms row by row.
- **`F` of the product.** By `rectangularFourierEquiv_apply` and
  `rectangularFourierIntegral_entryProduct`, the function underlying
  `F (entryProductTest g)` is
  `a ↦ ∏ i, ∏ j, fourierIntegral ψ μ (g i j) (a i j)`.
- **Both composites at `b`.** By the evaluation lemmas and the two function
  identities, the left side at `b` is
  `rectangularFourierIntegral ψ μ (fun a => ∏ i, ∏ j, g' i j (a i j)) b`.
  By `rectangularFourierIntegral_entryProduct` this is
  `∏ i, ∏ j, fourierIntegral ψ μ (g' i j) (b i j)`. The right side at `b` is
  the partial integral of `a ↦ ∏ i, ∏ j, fourierIntegral ψ μ (g i j) (a i j)`.
  By `partialFourierIntegral_entryProduct` this is
  `∏ i, (∏ k, fourierIntegral ψ μ (g i k.castSucc) (b i k.castSucc)) *
  fourierIntegral ψ μ (fourierIntegral ψ μ (g i (Fin.last n))) (-b i (Fin.last n))`.
  After `Fin.prod_univ_castSucc` on the left, the first `n` column factors
  coincide. The last-column factors are
  `fourierIntegral ψ μ (fun t => G (-t)) (b i (Fin.last n))` and
  `fourierIntegral ψ μ G (-b i (Fin.last n))`, with
  `G = fourierIntegral ψ μ (g i (Fin.last n))`. They are equal by
  `fourierIntegral_comp_neg`.

### `rectangularFourierCommutation`

This theorem proves the target. After introducing the telescope,
`matrixTensorDecomposition Φ` gives `M`, `c` and `g`. The pointwise identity is
promoted to the equality of Schwartz functions
`Φ = ∑ k, c k • entryProductTest (g k)`, by extensionality and
`entryProductTest_apply`. After rewriting `Φ`, `map_sum` and `map_smul` for the
linear equivalences `F` and `T` distribute both composites over the finite
sum. The two sums agree termwise by
`rectangularFourierCommutation_entryProduct`.

## Measures, hypotheses and degenerate rank

Every integral in the proof is against the supplied measures: the nested
product `RankinSelberg.rectangularMeasure μ n (n + 1)`, the finite product
`rowMeasure μ n` and the scalar `μ.measure`. The proof uses only their
definitional `Measure.pi` structure. No coordinate bijection, flattening or
pushforward measure is used. No product `BorelSpace` instance is installed.
The only derived instance is `SigmaFinite μ.measure`, from
`selfDualSigmaFinite`.

The theorem adds no premise to the target. In particular it adds no product
Borel, sigma-finiteness, second-countability, inversion-continuity, valuation,
p-adic or positive-rank hypothesis, and assumes no Fourier map,
product-measure compatibility, Fubini identity or commutation law. The
explicit `[SigmaFinite μ.measure]` hypothesis of the helper
`partialFourierIntegral_entryProduct` is discharged inside
`rectangularFourierCommutation_entryProduct` as described above.

The rank `n = 0` needs no separate case. The same argument applies verbatim:
products over `Fin 0` are empty, and the measures are the corresponding
finite products.

## Scope and source

The target Markdown explains that the statement is a derived chosen-map
formulation of the fact `(Φ~)^ = (Φ^)~` used without proof just before
formula (7) in H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, Amer. J. Math. 105 (1983), Section 6.1,
printed page 428 (registered as `jpss-1983-rankin-selberg`). This proof does
not follow a printed proof, since the source gives none. It does not prove
covariance of either transform, formula (7), or any other source statement.
It also does not evaluate the common value of the two sides beyond the
factorwise identity above.
