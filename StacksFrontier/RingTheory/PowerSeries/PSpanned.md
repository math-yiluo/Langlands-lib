# Spanning power series by Frobenius powers

Module `StacksFrontier.RingTheory.PowerSeries.PSpanned`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a perfect field κ of prime characteristic p, powers of the variable of exponent below p span κ⟦X⟧ over the subring of pth powers.

`PowerSeries.isPSpannedBy_X` proves the library’s `IsPSpannedBy p` condition for X. It gives, for each series f, a family of series gᵢ indexed by 0 ≤ i < p such that f is the sum of gᵢᵖXⁱ. The statement asserts existence of this expression.

The proof groups coefficients by their exponent modulo p and applies inverse Frobenius to the coefficients in each group. The power series expansion formula for Frobenius then identifies each coefficient of f with its contribution from the unique matching residue class.

The file cites this result as an input to condition (b) of Tag 09F9 for equal-characteristic complete discrete valuation rings with perfect residue field.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/PowerSeries/PSpanned.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
