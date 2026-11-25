# Equal-characteristic wild prime-degree solutions

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.WildCharP`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves the Artin–Schreier step of Epp’s theorem over a perfect residue field. When the Laurent coefficients lie in the perfect core, it absorbs their roots over one base and solves every reduced tensor factor.

`exists_finite_extension_isWeakSolution_of_constant_laurent_of_charP` works with a DVR tower A ⊆ B ⊆ C and fraction fields K ⊆ L ⊆ M of prime characteristic p. It assumes A and B complete, A → B weakly unramified, the base residue field perfect, `EppCondition A B p`, and M/L finite Galois. It takes an Artin–Schreier generator, a Laurent expansion of depth N with respect to a uniformizer from A, a residue section agreeing with a ring map modulo the N-th power of the maximal ideal, and `hperfect`, which puts every pole coefficient in the perfect core. It produces a weak solution for A → C over a finite extension of K.

`exists_finite_extension_isWeakSolution_of_wild_charP` assumes the same tower and residue conditions with Galois top degree p. It obtains a weak solution without needing any presentation as input. If a generating Artin–Schreier equation has integral parameter, the tower is already weakly unramified. Otherwise an earlier preparation gives either a direct solution or the Laurent data above.

The Laurent proof chooses pᴺ-th roots of the coefficients and uses one finite weakly unramified extension to supply their images in every reduced factor. Matching lower and upper factors gives degree one or p. Degree one uses weak unramifiedness of the lower layer, and degree p uses the transported Laurent presentation. The factor solutions are then combined.

The solver concerns the equal-characteristic degree-p layer, and the rings and fields in both statements share one universe.

References include Tag 09F0 for the integral Artin–Schreier criterion and Tag 09ET for the single-factor implication discussed in the comments.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppPrimeDegree/WildCharP.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
