# Finitely many generating sections on a spectrum give a finite module

Module `StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on modules on an affine scheme, an input to the characterization of coherent modules.

- `Stacks.AlgebraicGeometry.CoherentTFAE.finite_moduleSpecΓ_of_generatingSections`: for a quasi-coherent module `N` on `Spec A` with a family of generating sections `σ` indexed by a finite type, the global sections `moduleSpecΓFunctor.obj N` form a finite `A`-module.

Since `N` is quasi-coherent, its comparison map `N.fromTildeΓ` is invertible, so `σ` gives an epimorphism from a finite free sheaf onto the `~` of the global sections, and `finite_of_epi_free_tilde` (from the `Affine` file of the same directory) concludes.

## Watch for

- The hypothesis is a family of generating sections over the whole of `Spec A`, not local generators.
- The module docstring announces that finite type is local on a scheme and the identification of a quasi-coherent module on an affine open with the `~` of its sections, with the constructions for them. The file holds none of these; their sections are empty.

## References

Tag 01XZ, Tag 01PB, Tag 01B4.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/CoherentTFAE/Local.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 1 are kept. The 11 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
