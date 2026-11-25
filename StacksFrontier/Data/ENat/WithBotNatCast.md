# Natural number casts in extended naturals with bottom

Module `StacksFrontier.Data.ENat.WithBotNatCast`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one lemma about `WithBot ℕ∞`, which has both a bottom and a top element.

`natCast_ne_top_withBot` says that every natural number cast into this type differs from top. It uses injectivity of the inclusion of `ℕ∞` and `ENat.natCast_ne_top`.

The module docstring also lists a second result, which recovers a value other than bottom and top as the cast of a natural number; it is not in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Data/ENat/WithBotNatCast.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `eq_natCast_unbotD_toNat`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
