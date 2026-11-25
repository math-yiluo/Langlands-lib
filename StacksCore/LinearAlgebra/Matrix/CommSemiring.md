# Sub-regular pairs in a semiring

Module `StacksCore.LinearAlgebra.Matrix.CommSemiring`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a semiring there is no subtraction, so the file supplies a semiring notion of "`p − q` is a non-zero-divisor".

- `SubRegular p q`: for all `a, b`, `a * p + b * q = b * p + a * q` implies `a = b`.
- Over a ring it holds exactly when `p − q` is right-regular (`subRegular_iff_rightRegular_sub`, by way of `subRegular_iff_sub`: `SubRegular p q ↔ SubRegular (p − q) 0`); `SubRegular p 0` and `SubRegular 0 p` both say that `p` is right-regular.
- It is symmetric (`SubRegular.symm`, `SubRegular.comm`); in a nontrivial semiring it forces `p ≠ q` (`SubRegular.ne`).

Watch for:

- `SubRegular` is the library's own notion, not Mathlib's, and is one-sided: it concerns multiplication on the right by `p` and `q`.
- The file makes Mathlib's `isRegular_one` a simp lemma.
- The module docstring announces lemmas on permutations and signed-part determinants that the file does not contain.

References: for sub-regularity, the symmetrized-semiring literature, Plus (1990) and Butkovič–Gaubert (1999).

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/LinearAlgebra/Matrix/CommSemiring.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 41 declarations of the source file 8 are kept. The 33 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
