# Powers of an ideal after scalar extension

Module `StacksFrontier.RingTheory.AdicCompletion.SmulTopPow`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let S be a commutative R-algebra, I an ideal of the commutative ring R, and J its extension to S. The filtration by powers of I on an S-module agrees with that by powers of J after restriction of scalars.

`smul_top_pow_eq_restrictScalars_module` gives IⁿM = JⁿM as R-submodules when the R- and S-actions on M form a scalar tower. `quotEquivMapPowModule` gives the resulting R-linear isomorphism of quotients and sends each class to the class of the same element. For a commutative R-algebra U, `smul_top_pow_eq_restrictScalars` identifies IⁿU with the ideal (IU)ⁿ viewed over R, and `quotEquivMapPow` gives the corresponding quotient isomorphism.

The proofs use compatibility of ideal extension with powers and of the ideal action with restriction of scalars.

EGA 0 1.0.4.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 1.0.4 | `smul_top_pow_eq_restrictScalars_module` | JM = (BJ)M |
| EGA | 0 1.0.4 | `smul_top_pow_eq_restrictScalars` | commutative B and M = B |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/SmulTopPow.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
