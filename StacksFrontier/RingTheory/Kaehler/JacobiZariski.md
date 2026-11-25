# Left exactness of the sequence of differentials of a tower

Module `StacksFrontier.RingTheory.Kaehler.JacobiZariski`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a tower R → A → B of commutative rings, this file shows that the sequence 0 → B ⊗[A] Ω[A/R] → Ω[B/R] → Ω[B/A] → 0 of Kähler differentials is exact on the left when the first cotangent homology of B over A vanishes.

`KaehlerDifferential.mapBaseChange_injective` proves injectivity of B ⊗[A] Ω[A/R] → Ω[B/R] under `Subsingleton (Algebra.H1Cotangent A B)`. In the Jacobi–Zariski sequence this map is preceded by the connecting map from H₁(L_{B/A}), with exactness given by Mathlib's `Algebra.H1Cotangent.exact_δ_mapBaseChange`, so its kernel is zero. Mathlib supplies the middle exactness and the final surjection onto Ω[B/A].

The theorem provides the left-hand injectivity in Tag 04B2. Smoothness, and more generally formal smoothness, supplies its vanishing hypothesis. The module docstring also describes exactness of the Jacobi–Zariski sequence at H₁ of the cotangent complex (Tag 00S2), which the file does not prove.

References include Tag 04B2 and SGA 6 VIII 2.6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [04B2](https://stacks.math.columbia.edu/tag/04B2) | `KaehlerDifferential.mapBaseChange_injective` | Exactness at `C ⊗_B Ω_{B/A}`, the one node of the sequence that is not already in Mathlib; the other two are `KaehlerDifferential.exact_mapBaseChange_map` and `KaehlerDifferential.map_surjective`. Stated under `H₁(L_{C/B}) = 0`, the hypothesis the source's second proof uses, which the tag's smoothness gives by instance inference. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 6 VIII 2.6 | `KaehlerDifferential.mapBaseChange_injective` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Kaehler/JacobiZariski.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 1 are kept. The 3 left out are not needed by the results for which the extract is made: `Algebra.Generators.Cotangent.map_ker_baseChange_cotangentComplex`, `Stacks.KaehlerDifferential.JacobiZariski.solution`, `Stacks.KaehlerDifferential.LeftExactness.solution`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
