# Integrality in finite products

Module `StacksFrontier.RingTheory.IntegralClosure.Pi`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file shows that integrality in a finite product of commutative rings can be tested coordinatewise. It treats both a product of base rings and a single base ring.

- `isIntegral_pi_iff` takes a finite family of commutative algebras Sᵢ over Rᵢ and says that an element of the product of the Sᵢ is integral over the product of the Rᵢ exactly when each coordinate is integral over Rᵢ. The structure map acts componentwise by `algebraMap_pi_apply`.
- For a finite family of commutative algebras over one ring R, `isIntegral_pi_iff_const` gives the corresponding criterion over R, and `integralClosurePiEquiv` is the R-algebra equivalence between the integral closure in the product and the product of the integral closures.
- `isNilpotent_pi_iff` gives the coordinatewise nilpotence criterion for a finite product of commutative rings. Separately, `IsIdempotentElem.isIntegral` shows that an idempotent of an R-algebra is integral over R by the equation X² − X = 0.

Projection carries any monic equation to one in each factor. To combine coordinate equations over different bases, the proof multiplies each monic polynomial by a power of X to match the largest degree, then assembles the coefficients. For a fixed base, multiplying the monic polynomials gives a common equation.

The varying-base integrality criterion is Tag 0CY8. The module docstring also lists a variant indexed by `Fin n`, which is not in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0CY8](https://stacks.math.columbia.edu/tag/0CY8) | `isIntegral_pi_iff` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/IntegralClosure/Pi.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 6 are kept. The 1 left out are not needed by the results for which the extract is made: `isIntegral_pi_fin_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
