# Local rings at generic points of irreducible components

Module `StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Two lemmas on a scheme `W` and a generic point `y` of one of its irreducible components (`y : genericPoints W`).

- `Stacks.Chow.isMax_of_mem_genericPoints`: `y` is maximal for the specialization order, that is, every point of which `y` is a specialization equals `y`. The proof is `Topology.eq_of_specializes_isGenericPoint`.
- `Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints`: the local ring `𝒪_{W,y}` has Krull dimension zero. By Mathlib's `ringKrullDim_stalk_eq_coheight` this dimension is the coheight of `y`, which vanishes because `y` is maximal.

## Watch for

- In the specialization order on the points of a scheme, `x ≤ y` means `y ⤳ x`.
- The module docstring presents the file as discharging the two dimension hypotheses of the local comparison of multiplicities behind Tag 02S5, at points of the fibres of a family over `ℙ¹`, and lists results for them and a converse of the first lemma. The file holds none of these; its sections on the two hypotheses are empty.

## References

See the table below.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 2.4.3 | `ringKrullDim_stalk_eq_zero_of_mem_genericPoints` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/FibreDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 2 are kept. The 7 left out are not needed by the results for which the extract is made: `Stacks.Chow.coheight_eq_one_of_strictMono_of_le_of_eq`, `Stacks.Chow.exists_le_zero_of_exists_eq_stalk`, `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_le_zero_infinityFiber`, `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_le_zero_zeroFiber`, `Stacks.Chow.mem_genericPoints_of_isMax`, `Stacks.Chow.ringKrullDim_quotient_idealStalk_eq_one`, `Stacks.Chow.ringKrullDim_stalk_subscheme_eq_one`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
