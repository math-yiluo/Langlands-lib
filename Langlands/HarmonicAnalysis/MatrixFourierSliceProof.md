# Proof of the rectangular Fourier slice

Author: Worker 731.

The theorem `Langlands.HarmonicAnalysis.padicMatrixFourierSlice` proves
exactly the published proposition
`Langlands.HarmonicAnalysis.PadicMatrixFourierSliceStatement.{u}`.
The statement module and the modules it imports are unchanged.

The statement is conditional. For a prime `p`, `F : PadicField.{u} p`,
`T : F.TopologicalData` and `a b : ℕ`, the theorem assumes
`PadicRowFourierSurjectivityStatement F T (b + 1)`. It installs `T.topology`
and the Borel measurable space on `F.Carrier`. For every unitary additive
character `ψ`, scalar additive Haar measure `ν` and
`Φ : SchwartzBruhat (Fin (b + 1) → F.Carrier)`, it constructs one
`Ψ : SchwartzBruhat (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier)` such that,
for every `g : GeneralLinear (b + 1) F.Carrier`,

```
∫ x, ψ.complex (-(x (Fin.last b) 0)) * Ψ (g⁻¹.val * x)
    ∂RankinSelberg.rectangularMeasure ν (b + 1) (a + 1)
  = (T.normalizedAbs (det g.val) : ℂ) ^ (a + 1) * Φ (RankinSelberg.lastRow g).
```

The proof does not prove the row surjectivity hypothesis. It uses only the
`b + 1` instance given as the hypothesis.

## Helpers

These declarations, in section `Columns`, work over any topological field `K`.

- `matrixColumns r s` is the continuous additive equivalence from
  `Matrix (Fin r) (Fin s) K` to `Fin s → Fin r → K` that sends a matrix to its
  family of columns, `Y ↦ (j ↦ (i ↦ Y i j))`.
- `columnProduct h`, for `h : Fin s → SchwartzBruhat (Fin r → K)` over a
  Hausdorff `K`, is the Schwartz–Bruhat function
  `Y ↦ ∏ j, h j (column j of Y)`. It is locally constant because each factor is
  the composite of a locally constant function with a continuous map. Its
  support is contained in the preimage under `matrixColumns` of the product of
  the supports `tsupport (h j)`, and that preimage is compact.
  `columnProduct_apply` records the defining formula.
- `exists_columnProduct_integral` assumes in addition that `K` is Borel,
  second countable and locally compact. Let `μ` be any additive Haar measure on
  `Matrix (Fin r) (Fin s) K` and `ν` any scalar additive Haar measure. Then
  there is a real `c > 0` (in `ℝ≥0`) such that for every family
  `f : Fin s → (Fin r → K) → ℂ`

  ```
  ∫ Y, ∏ j, f j (column j of Y) ∂μ = c * ∏ j, ∫ v, f j v ∂rowMeasure ν r.
  ```

  Proof: the pushforward of `μ` along `matrixColumns` is an additive Haar
  measure on `Fin s → Fin r → K`, as is the product
  `Measure.pi (fun _ => rowMeasure ν r)`. Mathlib's additive Haar uniqueness
  `Measure.isAddLeftInvariant_eq_smul` makes the first a multiple of the
  second by `Measure.addHaarScalarFactor`. That factor is positive by
  `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure`. The integral is
  transported with `integral_map_equiv`. It is then split with
  `integral_smul_nnreal_measure` and `integral_fintype_prod_eq_prod`. The
  identity holds for all `f`, including nonintegrable ones, because both
  Mathlib lemmas hold without integrability hypotheses. No transposition of a
  rows-first product measure is needed: Haar uniqueness compares the two
  measures directly.

## Main proof

Write `B = b + 1`, `A = a + 1`, `μ = rectangularMeasure ν B A` and
`l = lastRow g`.

1. **Instances.** The proof installs `T.topology`, `T.valuativeRel` and
   `T.localField`. It takes second countability from `T.secondCountableTopology`
   and the Hausdorff property from `T.fieldT2`, and uses `borel F.Carrier` with
   its `BorelSpace` instance. These are the topology and measurable space of the
   statement.
2. **Cutoff of integral rows.** Let `O` be the ring of integers `T.Integers`.
   It is open and compact (`T.isOpen_integers`, `T.isCompact_integers`).
   `S = {v | ∀ i, v i ∈ O}` is clopen and compact in `Fin B → F.Carrier`, and
   `κ₀ = Hecke.TestFunction.characteristic` of `S`. Its row integral
   `I₀ = ∫ κ₀ d(rowMeasure ν B)` is the real measure of `S`. `I₀` is nonzero
   because `S` is open and contains `0`, so has positive measure by
   `IsOpen.measure_pos`, and is compact, so has finite measure.
3. **Normalization.** `exists_columnProduct_integral` with `μ` and `ν` gives
   `c > 0`. Let `C = c * I₀ ^ a`. Then `C ≠ 0`.
4. **Row kernel.** Let `Φ' = C⁻¹ • (Φ ∘ neg)`, written as `C⁻¹` times
   `Hecke.TestFunction.pullback (Homeomorph.neg _) Φ`. The hypothesis
   `PadicRowFourierSurjectivityStatement F T B`, applied to `ψ`, `ν` and `Φ'`,
   gives `κ` with `IsRowFourierPair ψ ν κ Φ'`. Thus for every `y`,
   `Φ' y = ∫ ψ(rowPairing x y) κ(x) d(rowMeasure ν B)(x)`.
5. **Choice of `Ψ`.** `Ψ = columnProduct (Fin.cons κ (fun _ => κ₀))`. It has
   `κ` in the first column and `κ₀` in each of the other `a` columns. `Ψ` does
   not depend on `g`.
6. **Change of variables.** Let
   `G y = ψ(-((g.val * y) last 0)) * Ψ y`. Since `g * (g⁻¹ * x) = x`, the
   integrand of the statement is `G (g⁻¹.val * x)`. By `integral_map`, the
   integral equals `∫ G` against the pushforward of `μ` along
   `x ↦ g⁻¹.val * x`. The published `padicRectangularHaarScaling`, applied with
   `A = g⁻¹` and `B = 1`, identifies that pushforward as
   `(T.determinantNorm g) ^ (a + 1) • μ`. This uses the inverse of the
   determinant character, `Units.val_inv_eq_inv_val` and `inv_inv`. Then
   `integral_smul_nnreal_measure` extracts the scalar factor.
7. **Column factorization.** The entry `(g.val * y) last 0` is
   `Σ_k g last k * y k 0`. Hence
   `-((g.val * y) last 0) = rowPairing (column 0 of y) (-l)`. So `G` is the
   column product of
   `f 0 = (v ↦ ψ(rowPairing v (-l)) * κ v)` and `f (j+1) = κ₀`
   (`Fin.prod_univ_succ`). By step 3,
   `∫ G dμ = c * (rowFourierIntegral ψ ν B κ (-l) * I₀ ^ a)`.
8. **Conclusion.** By step 4, `rowFourierIntegral ψ ν B κ (-l) = Φ' (-l)`,
   and `Φ' (-l) = C⁻¹ * Φ l` by `neg_neg`. So
   `c * (C⁻¹ * Φ l * I₀ ^ a) = Φ l`. The real factor
   `T.determinantNorm g` coerces to `T.normalizedAbs (det g.val)` by
   `T.determinantNorm_coe`. This gives the statement's right-hand side.

All integrals in the proof are Bochner integrals. Every manipulation uses an
identity that holds without integrability hypotheses (`integral_map` for a
continuous integrand and a measurable map, Haar uniqueness, scalar
multiplication of measures, and the finite-product formula). The case `a = 0`
is included: then `Ψ = κ` on the single column, the product over the other
columns is empty, and `I₀ ^ 0 = 1`.

## Provenance

This proof is for the derived statement extracted from Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983), proof of
the Proposition in Section (9.1), printed pp. 453–454
(`jpss-1983-rankin-selberg`). The source substitutes `x = g y`, picks up the
Jacobian `|det g|^{r₁}`, and recognizes the trace Fourier transform `Φ'` at
`-η g`; the column-0 pairing in step 7 is the scalar shape of that step. The
source then chooses `Ψ` with `Φ'(-η g) = Φ(η g)` without further detail.
Choosing `Ψ` as a column product is this proof's own construction. A row
Fourier kernel goes in one column, and normalized characteristic functions of
integral rows go in the others. With this choice the matrix Fourier transform
is never needed: only the row transform in dimension `b + 1`, supplied by the
hypothesis.

The imported published results are `padicRectangularHaarScaling`
(`Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`),
`T.determinantNorm_coe`, `T.isOpen_integers`, `T.isCompact_integers`,
`T.secondCountableTopology`, `Hecke.TestFunction.characteristic` and
`Hecke.TestFunction.pullback`, together with Mathlib's Haar uniqueness,
finite-product integration and integration with respect to pushforward
measures.
