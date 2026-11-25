# Quotients of an adic completion by powers of an ideal

Module `StacksFrontier.RingTheory.AdicCompletion.QuotPow`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let M be a module over a commutative ring R and let I be a finitely generated ideal of R. Reduction at level n identifies the quotient of the I-adic completion of M by its submodule of Iⁿ-multiples with M/IⁿM.

`AdicCompletion.bijective_liftQ_eval` proves bijectivity of the map induced by the level-n projection. `AdicCompletion.quotPowSMulTopEquiv` packages it as an R-linear isomorphism sending the class of a coherent sequence to its nth component.

The level projection is surjective. Injectivity on the quotient uses `AdicCompletion.pow_smul_top_eq_ker_eval`, where finite generation identifies the kernel with the submodule of Iⁿ-multiples.

The comparison covers every natural n, including zero, and applies to arbitrary R-modules. It gives the quotient assertion of Tag 05GG. At M = R the comparison here is R-linear. The R-algebra version is `AdicCompletion.quotMapPowAlgEquiv`, cited in the file.

Tag 05GG attributes the lemma to Matlis, Theorem 15, and the proof using generators to Bjorn Poonen. Tag 05JA is cited for the failure of the quotient comparison without finite generation.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/QuotPow.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `AdicCompletion.pow_smul_top_eq_restrictScalars_range_ofPowSMul`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
