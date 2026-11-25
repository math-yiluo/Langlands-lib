# Continuity for adic topologies

Module `StacksFrontier.Topology.Algebra.AdicTopology.Continuous`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`RingHom.continuous_adic_iff` characterizes continuous ring homomorphisms φ from a commutative ring R with the I-adic topology to a commutative ring S with the J-adic topology. Continuity is equivalent to φ(Iⁿ) being contained in J for some natural number n ≥ 1.

The proof tests continuity at zero using the two power bases. Continuity gives the condition at the neighborhood J, and taking powers of the containment gives φ((Iⁿ)ᵐ) ⊆ Jᵐ for every m.

Reference is Stacks Project Lemma 15.37.2, Tag 07E9.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07E9](https://stacks.math.columbia.edu/tag/07E9) | `RingHom.continuous_adic_iff` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Algebra/AdicTopology/Continuous.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
