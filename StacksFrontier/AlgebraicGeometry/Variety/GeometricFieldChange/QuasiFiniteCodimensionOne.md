# Generic points lie in every dense open

Module `StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Every generic point of an irreducible component lies in every dense open subset, in a Noetherian space and in a locally Noetherian scheme.

- `AlgebraicGeometry.genericPoints_mem_dense_open` proves this in a Noetherian topological space. The component of which y is the generic point has a nonempty open subset, which meets the dense open, and y specializes to every point of that subset.
- `scheme_genericPoints_mem_dense_open` gives the same for a locally Noetherian scheme, which need not be a Noetherian space, by applying the first lemma on an affine open containing the point, where it is still a generic point.

The module docstring describes quasi-finiteness over a point whose local ring is Noetherian of dimension at most one, and finiteness of a proper morphism over a neighbourhood of such a point (Tags 0AB6 and 0AB7); none of those results is in the file. EGA 0 2.1.4 is cited for the first lemma.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 2.1.4 | `genericPoints_mem_dense_open` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/GeometricFieldChange/QuasiFiniteCodimensionOne.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 2 are kept. The 7 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.eq_of_specializes_genericPoint`, `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one`, `AlgebraicGeometry.fiber_isLocallyNoetherian`, `AlgebraicGeometry.quasiFiniteAt_iff_topologicalKrullDimAt_fiber_eq_zero`, `AlgebraicGeometry.quasiFiniteAt_of_genericPoint_of_isAlgebraic`, `AlgebraicGeometry.quasiFiniteAt_of_genericPoint_of_isLocallyNoetherian_dense`, `AlgebraicGeometry.quasiFiniteAt_of_target_stalk_dimension_le_one`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
