# Characteristic of an endomorphism semiring

Module `StacksCore.Algebra.CharP.LinearMaps`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A version of Mathlib's `Module.charP_end` whose hypotheses are that the base semiring is a domain and the module is nontrivial and torsion-free.

- `Module.charP_end'` (instance): let `R` be a commutative semiring that is a domain, of characteristic `p`, and `M` a nontrivial torsion-free `R`-module. Then the semiring `M →ₗ[R] M` of `R`-linear endomorphisms of `M` has characteristic `p`.

The proof picks a nonzero element of `M` and applies `Module.charP_end` to it.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/Algebra/CharP/LinearMaps.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
