# Smoothness from adic formal smoothness of DVR stalks

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DiscreteValuationStalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A flat morphism locally of finite presentation is smooth at a point if its stalk map is an adically formally smooth extension of discrete valuation rings. Two variants let the stalk map be given by an isomorphic model.

- `smoothAt_of_formallySmoothNAdic_stalkMap` assumes the source and target local rings at x and f(x) are domains and discrete valuation rings. The hypothesis `h` requires `RingHom.FormallySmoothNAdic` for the stalk map with respect to the maximal ideal of the local ring of X at x. The conclusion is `InfinitesimalLifting.SmoothAt f x`.
- `smoothAt_of_formallySmoothNAdic_of_arrowEquiv` accepts a ring map φ between local rings as a model of the stalk map. The two ring equivalences `eA` and `eB` commute with the map by `hcomm`. Formal smoothness for the maximal ideal of the target of φ transfers to the stalk map.
- `smoothAt_of_formallySmoothNAdic_localRingHom` uses the model Aₚ → B_q for an A-algebra B, with p the contraction of q. The compatibility `hbase` is stated on elements of A. The universal property of localization extends it to the full square.

Flatness of the local stalk map gives faithful flatness. The criterion for DVR extensions yields weak unramifiedness and a separable residue extension. These identify the local fibre ring with the residue field and give formal smoothness of the residue-field map, so the flat closed-fibre criterion applies.

The localization result supplies the smoothness step in the reduced fibre theorem. In that application, the model equivalences and `hbase` are inputs, and `h` is the adic formal smoothness supplied by the solution property in Tag 09EN(2).

Stacks Project, Tag 09E7, Tag 01V9, Tag 09EM, Tag 09EN and Tag 09IL. EGA IV 17.5.1.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.5.1 | `smoothAt_of_formallySmoothNAdic_stalkMap` | c)⇒a) |
| EGA | IV 17.5.1 | `smoothAt_of_formallySmoothNAdic_of_arrowEquiv` | c)⇒a) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/DiscreteValuationStalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
