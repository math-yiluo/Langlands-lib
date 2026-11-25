# The structure sheaf of a scheme is quasi-coherent

Module `StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Two results: the structure sheaf of a scheme is quasi-coherent as a module over itself.

- `isQuasicoherent_unit_of_isoSpec`: for `e : Y ≅ Spec R`, the structure sheaf `SheafOfModules.unit Y.ringCatSheaf` is quasi-coherent. On `Spec R` this is `isQuasicoherent_iff_isIso_fromTildeΓ`; it is carried to `Y` by restriction along `e.hom` (`Scheme.Modules.isQuasicoherent_restrictFunctor`) and `Scheme.Modules.restrictUnitIso`.
- `isQuasicoherent_unit` (an instance): for every scheme `X`, the structure sheaf is quasi-coherent. It is checked on the affine opens, by the library's `QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens`, using the previous lemma.

Both are in the namespace `Stacks.AlgebraicGeometry.AffineQcohPushforward`.

## Watch for

- The module docstring announces the pushed-forward sheaf of rings `f_* 𝒪_X`, the direct image as a module over it, and the quasi-coherence results drawn from Tags 02KG, 01SB and 0H88. The file holds none of these, only the quasi-coherence of the structure sheaf.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/AffineQcohPushforward/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 2 are kept. The 7 left out are not needed by the results for which the extract is made: `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_pushforwardModules_of_reflects`, `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforward`, `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforwardRing`, `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules`, `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules_unit`, `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`, `Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
