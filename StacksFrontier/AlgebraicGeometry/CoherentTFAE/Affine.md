# A finite free sheaf onto `M^~` makes `M` a finite module

Module `StacksFrontier.AlgebraicGeometry.CoherentTFAE.Affine`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

On `Spec R`, the file shows that an `R`-module `M` is finite as soon as the sheaf `M^~` receives an epimorphism from a finite free sheaf of modules. This is one direction of the affine dictionary between finite modules and finitely generated sheaves, an input to the characterization of coherent modules on a locally Noetherian scheme.

## Results

- `finite_of_epi_free_tilde`: for an `R`-module `M`, a finite type `ι : Type u` and an epimorphism `p : free ι ⟶ M^~` of sheaves of modules on `Spec R` (passed as an explicit proof `hp : Epi p`), `M` is a finite `R`-module.
- `epi_of_map_epi`: a faithful functor reflects epimorphisms; this is Mathlib's `Functor.epi_of_epi_map`, with the hypothesis an explicit argument.

## Proof

Composing `p` with the isomorphism `tildeFinsupp ι` between `(ι →₀ R)^~` and `free ι` gives an epimorphism out of `(ι →₀ R)^~`. Since `~` is full, it is the image of a map `(ι →₀ R) ⟶ M`, which is surjective because the faithful functor `~` reflects epimorphisms. A private lemma composes an isomorphism, given by an explicit `IsIso` proof, with an epimorphism.

## Watch for

- `Epi` and `IsIso` facts are passed as explicit proofs because instance search does not find them on morphisms of `(Spec R).Modules`; the module docstring explains why.
- The module docstring also announces that finitely many global generating sections give finite type on any site, that `M^~` is of finite type when `M` is finite, and the case of global generating sections of `M^~`. The file holds none of these; its section on sites is empty.

## References

Tag 01XZ, Tag 01B4, Tag 01PB.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/CoherentTFAE/Affine.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 3 are kept. The 6 left out are not needed by the results for which the extract is made: `Stacks.AlgebraicGeometry.CoherentTFAE.epi_tildeFreeHom`, `Stacks.AlgebraicGeometry.CoherentTFAE.finite_of_generatingSections_tilde`, `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_generatingSections`, `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_tilde`, `Stacks.AlgebraicGeometry.CoherentTFAE.tildeFreeHom`, `Stacks.AlgebraicGeometry.CoherentTFAE.tildeGeneratingSections`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
