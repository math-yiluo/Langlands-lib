# Quasi-coherence is checked on affine opens

Module `StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One lemma on modules on a scheme.

- `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens`: a module `M` on a scheme `X` whose restriction to every affine open `V` (`(Scheme.Modules.restrictFunctor V.ι).obj M`) is quasi-coherent is quasi-coherent.

The affine opens cover `X` (`iSup_affineOpens_eq_top`); on each, the library's `AffinePushforward.nonempty_presentation_of_isoSpec` gives a presentation of the restriction from its quasi-coherence, and `AffinePushforward.isQuasicoherent_of_presentations` concludes.

## Watch for

- The module docstring announces that quasi-coherent modules are closed under colimits, with cokernels and coproducts as special cases. The file holds none of these, only the locality lemma above; the variable `K` and the hypothesis on colimits in module categories that it declares are not used.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/AffineQcohPushforward/Colimits.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 1 are kept. The 8 left out are not needed by the results for which the extract is made: `Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape`, `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`, `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`, `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit`, `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit_of_isoSpec`, `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit_spec`, `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_restrictFunctor_obj_of_isColimit`, `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
