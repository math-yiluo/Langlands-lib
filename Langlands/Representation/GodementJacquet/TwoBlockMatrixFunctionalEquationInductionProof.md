# Proof of the conditional two-block normalized matrix functional equation

Module `Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionProof`.
The matched expansion uses the dual-side modules `TwoBlockDualParabolicIntegral`,
`InverseTransposeMatrixIntegral` and `RectangularFourierUnimodularTranslate`.

## Result

`Langlands.GodementJacquet.twoBlockMatrixFunctionalEquationInduction` proves exactly the
published proposition
`Langlands.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement.{uF,uV}`
(module `Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement`),
with its telescope unchanged. For two smooth admissible blocks of a canonical p-adic
field carrying the published normalized block matrix functional-equation data, the
actual normalized induced representation carries the same data with the product
polynomials, the product epsilon unit and the summed exponent. This is the
functional-equation part of Godement–Jacquet 1972, Theorem 3.4, for two blocks.

## Proof

The proof is one term:

```text
twoBlockMatrixFunctionalEquationInduction_of_expansion twoBlockMatchedZetaExpansion
  twoBlockMatrixAnalyticInduction
```

It combines three published results.

1. `twoBlockMatrixFunctionalEquationInduction_of_expansion`
   (module `TwoBlockFunctionalEquationAssembly`) proves the target from two
   hypotheses: the internal matched-expansion interface
   `TwoBlockMatchedZetaExpansionStatement` and the published analytic statement
   `TwoBlockMatrixAnalyticInductionStatement`. Its Markdown describes the reduction:
   the analytic conjuncts come from the analytic statement; the expansion is extended
   from the generators `biSmoothCoefficient I ℓ v` to the whole coefficient space by
   span induction, on the convergence half-planes of the analytic statement; and the
   block functional equations are multiplied by
   `normalizedFunctionalEquation_of_eventually_sum_mul` (module
   `FunctionalEquationProducts`).
2. `twoBlockMatchedZetaExpansion` (module `TwoBlockMatchedZetaExpansion`) proves the
   interface. For a generator coefficient `f`, the zeta integral of `(Φ, f)` and the
   zeta integral of the Fourier transform of `Φ` against `coefficientIota f` are
   finite sums of products of block zeta integrals, with the same finite data.
3. `twoBlockMatrixAnalyticInduction` (module `TwoBlockMatrixAnalyticInductionProof`)
   proves the analytic statement.

## Instance names in `TwoBlockMatchedZetaExpansion`

The `local instance`s of the published module `TwoBlockMatchedZetaExpansion` in the
namespace `Langlands.GodementJacquet.TwoBlock` have explicit names,
`matchedExpansionTopology`, …, `matchedExpansionGLBorel`. Anonymous, they would
receive the same auto-generated names as the anonymous local instances of the
published `TwoBlockReverseRealization`, which is imported by
`TwoBlockMatrixAnalyticInductionProof`; then no module could import both, and this one
must. The mathematics of that module is not affected. Its Markdown states the
convergence hypotheses for every test function of the block size and calls the finite
index type `J` (`ι` there denotes `coefficientIota`). Its module docstring cites
printed pages 37–42, as its Markdown does.

Compiled with 0 errors and 0 warnings. Axioms of
`twoBlockMatrixFunctionalEquationInduction`: `propext`, `Classical.choice`,
`Quot.sound`.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionProof` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
