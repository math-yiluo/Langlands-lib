# Germs of pulled-back sections and the stalk map

Module `StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.StandardSmooth`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one lemma. Let f : X ⟶ S be a morphism of schemes, x a point of X, and U, V opens of X and S with x ∈ U and U ⊆ f⁻¹(V). `Stacks.RelativeDifferentialStalkMap.appLE_germ_eq_germ_stalkMap` says that pulling a section over V back to U along f (`f.appLE V U`) and taking its germ at x gives the same as taking its germ at f(x) and applying the stalk map `f.stalkMap x`. The proof is a rewrite with Mathlib’s `Scheme.Hom.germ_stalkMap` and the compatibility of germs with restriction.

The module docstring announces that conditions (1) and (5) of Tag 01V9 imply conditions (3) and (4), together with bounds on the number of generators of modules of Kähler differentials (and cites Tag 00T7); none of these results is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/RelativeDifferentialStalkMap/StandardSmooth.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 1 are kept. The 9 left out are not needed by the results for which the extract is made: `Stacks.RelativeDifferentialStalkMap.condition1_imp_condition3`, `Stacks.RelativeDifferentialStalkMap.condition1_imp_condition4`, `Stacks.RelativeDifferentialStalkMap.fiberDimensionAt_eq_of_submersivePresentation`, `Stacks.RelativeDifferentialStalkMap.generatedByAtMost_kaehler_localization`, `Stacks.RelativeDifferentialStalkMap.generatedByAtMost_kaehler_of_submersivePresentation`, `Stacks.RelativeDifferentialStalkMap.generatedByAtMost_of_isLocalizedModule`, `Stacks.RelativeDifferentialStalkMap.generatedByAtMost_of_span_image`, `Stacks.RelativeDifferentialStalkMap.generatedByAtMost_of_surjective`, `Stacks.RelativeDifferentialStalkMap.natCard_compl_range_map`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
