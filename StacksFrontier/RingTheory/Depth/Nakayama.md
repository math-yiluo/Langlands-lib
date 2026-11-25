# Nakayama’s lemma for a local ring

Module `StacksFrontier.RingTheory.Depth.Nakayama`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file states Nakayama’s lemma for the maximal ideal of a local ring.

`Module.maximalIdeal_smul_top_ne_top` says that 𝔪M ≠ M for a nonzero finite module over a commutative local ring with maximal ideal 𝔪. It applies Nakayama’s lemma using the Jacobson radical of the annihilator.

The module docstring also lists a criterion for depth at least one in terms of a nonzerodivisor, with Tag 00LI as its reference; the file does not contain it.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/Nakayama.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `Module.one_le_depth_iff_exists_isSMulRegular`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
