# The support of a ring over itself and the dimension of a full support

Module `StacksFrontier.RingTheory.CohenMacaulay.Support`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file identifies the support of a ring over itself and the support dimension of a module of full support.

- `Module.support_self` gives full support for every commutative ring over itself, including the zero ring.
- `Module.supportDim_eq_ringKrullDim_of_support_eq_univ` identifies support dimension with ring dimension for a module of full support.

The self-support proof uses the zero annihilator of the faithful action. The dimension comparison bounds `dim Supp(M)` by `dim R` and, for the reverse inequality, maps `Spec R` strictly monotonically into the support, which is all of it.

The module docstring also lists two results on the invariance of the support dimension under ring isomorphisms; they are not in this file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/Support.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 2 are kept. The 3 left out are not needed by the results for which the extract is made: `Module.mem_support_iff_of_semilinearEquiv`, `Module.supportDim_eq_of_ringEquiv`, `Module.supportDim_eq_of_semilinearEquiv`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
