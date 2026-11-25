# Affine base change of associated sheaves

Module `StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a map φ from a commutative ring R to a commutative ring T, pulling the sheaf associated to an R-module back from Spec R to Spec T corresponds to extending scalars along φ.

`Stacks.AlgebraicGeometry.SectionsColimit.pullbackSectionsIso` identifies two functors to R-modules on sheaves of modules over Spec T. `pullbackSections` takes global sections of the direct image along `Spec.map`. `sectionsRestrictScalars` takes global sections on Spec T and restricts scalars. Naturality of the identification of the global functions on an affine spectrum with its ring gives equality of the scalar actions.

Both tilde followed by pullback and extension of scalars followed by tilde are left adjoint to `pullbackSections`. By uniqueness of left adjoints, `tildePullbackIso` naturally identifies the pullback of the sheaf associated to an R-module M with the sheaf associated to T ⊗ᵣ M. The instance `isQuasicoherent_pullback_specMap` shows that the pullback of a quasi-coherent sheaf remains quasi-coherent.

The module docstring also lists identifications of the global sections of the pullback; they are not in the file.

Stacks Project, Tag 01BG.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/SectionsColimit/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 13 declarations of the source file 9 are kept. The 4 left out are not needed by the results for which the extract is made: `Stacks.AlgebraicGeometry.SectionsColimit.moduleSpecΓ_smul`, `Stacks.AlgebraicGeometry.SectionsColimit.pushforward_app_smul`, `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`, `Stacks.AlgebraicGeometry.SectionsColimit.tildeSectionsPullbackIso`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
