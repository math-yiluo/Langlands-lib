# Proof: discrete-series coefficients of block Levis below exponent two

Author: Worker 246.

This module proves

```text
theorem Langlands.glProductLeviSquareIntegrableLp :
    GLProductLeviSquareIntegrableLpStatement.{uF, uW}
```

for the statement of
[`ProductLeviSquareIntegrableLpStatement`](ProductLeviSquareIntegrableLpStatement.md).
The field and representation universes `uF` and `uW` are independent. Auxiliary
declarations are in the namespace `Langlands.ProductLeviSquareIntegrable`. The
statement is imported by its Lean name and is not modified.

## Scope

Take a prime `p`, `F : PadicField p` with topological data `T`, a positive rank
`n` and a block shape `B`. Put `M = B.Levi F.Carrier` with
`T.leviTopologicalGroup B` and `Q = M ⧸ Subgroup.center M`. Fix a Borel
measurable structure and a Haar measure `μ` on `Q`. Let `σ` be a representation
of `M` with `IsSquareIntegrableModCenter σ μ`. Then for every
`c : UnitaryCentralCharacter σ`, `ℓ : SmoothDual σ` and `w`, the theorem gives
a real `r` with `1 < r < 2` and
`MemLp (c.coefficientNorm ℓ w) (ENNReal.ofReal r) μ`. The exponent depends on
`(ℓ, w)`. The irreducibility hypothesis of the statement is not used. Only the
admissibility and the `L²` coefficients contained in
`IsSquareIntegrableModCenter σ μ` are used.

## Route

1. Strict exponents.
   `strictFundHypothesis_of_squareIntegrable` of
   [`ProductLeviSquareIntegrableExponent`](ProductLeviSquareIntegrableExponent.md)
   turns `IsSquareIntegrableModCenter σ μ` into `StrictFundHypothesis T B σ`.
   This says that every generalized Jacquet eigencharacter has norm strictly
   less than `1` at every fundamental coweight `(ϖ, 1)` of every refinement
   `(k, C.size j - k)`.
2. Strict chamber bound. `strict_cell_coefficient_bound` of
   [`ProductLeviStrictChamberBound`](ProductLeviStrictChamberBound.md) gives
   `ε > 0` and `cb` with

   ```text
   ‖ℓ(σ(k₁ · leviRep lam · k₂) w)‖ ≤ cb · ∏ j, delta T (lam j) ^ (1/2 + ε)
   ```

   for all blockwise normalized `lam` and `k₁, k₂` in the integral Levi.
3. Integration (`memLp_of_strict`, stated for any block shape `C` and applied
   with `C = B`). The argument is the `L^(2+ε)` estimate in
   the published proof of `ProductLeviTempered.tempered_of_cellCount`, with
   another exponent:

   - `P = 2 (1 + ε) / (1 + 2 ε)` satisfies `1 < P < 2` and
     `(1/2 + ε) P - 1 = ε`.
   - With `w_s = fundWeight T C s ∈ (0, 1)` and `y_s = w_s ^ (1/2 + ε)`, the
     coefficient norm is at most `|cb| ∏ s, y_s ^ m s` on the cell
     `cellQ (latticeTuple m)` (`prod_delta_latticeTuple`).
   - The published `measure_cellQ_le`, from the Cartan coset count, bounds the
     cell measure by `∏ j, cc_j · delta(lam_j)⁻¹` times the finite measure of
     the image of the integral Levi.
   - The `P`-th power of the bound times the cell measure is at most a constant
     times `∏ s, x_s ^ m s`, where `x_s = y_s ^ P w_s⁻¹ = w_s ^ ε < 1`.
   - `finiteNatLatticeENNRealSummability` sums these terms over
     `FundIndex C → ℕ`. The cells cover `Q` (`exists_cell`,
     `latticeTuple_fundCoeff`). `countableCellLpUpper` gives `MemLp` for
     `ENNReal.ofReal P`. Almost-everywhere strong measurability comes from
     `UnitaryCentralCharacter.aestronglyMeasurable_coefficientNorm`.

The final theorem introduces the binders of the statement and applies
`memLp_of_strict` with the published proof
`GeneralLinear.CartanQuotient.cartanCellCount` of the cell count, admissibility
`hsq.1`, and the strict exponent hypothesis from step 1.

## Independence

The proof uses only the modules listed above and their imports: the published
product-Levi chamber, tempered-sufficiency and tempered-necessity helpers, the
refined upper compression, the Cartan decomposition and cell count, and the
countable-cell `L^p` criterion. It does not use the tempered discrete-series
isotypic statement or its reduction, any Jacquet quotient criterion for discrete
series, Langlands head or exhaustion theorems, or any classification of
square-integrable representations.

## Provenance

The statement Markdown derives the target from the proof of Waldspurger 2003
(`waldspurger-2003-plancherel`), Corollary III.1.2 (printed pp.263–264). The
open-cone exponent condition there (Proposition III.1.1, citing Casselman 1995
Theorem 4.4.6) gives exponential decay beyond `δ ^ (1/2)` on the chamber, and
the upper volume bound `vol(K a K) ≤ C δ(a)⁻¹` then makes the lattice sum of
`|f| ^ r` converge for `r < 2` close to `2`. The Lean proof follows this
outline. Its steps 1 and 2 are the Library's compression and cell-counting
arguments instead of Waldspurger's `Ξ` estimates, as described in the helper
modules.
