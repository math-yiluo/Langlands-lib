# Finite affine refinements of fpqc coverings of an affine scheme

Module `StacksFrontier.AlgebraicGeometry.FlatBaseChange.Descent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Two results on an fpqc covering of an affine scheme `S`, the steps by which descent along such a covering is reduced to descent along one faithfully flat map of affine schemes.

- `Stacks.AlgebraicGeometry.FlatBaseChange.exists_finite_affine_refinement`: a cover `𝒰` of `S` for `Scheme.fpqcPrecoverage` is refined by a flat affine cover `𝒱` (`Scheme.AffineCover @Flat S`) with finitely many members, the refinement maps `f.h₀ j` being open immersions. It comes from the quasi-compactness of the covering (`QuasiCompactCover.exists_hom`), `S` being compact.
- `Stacks.AlgebraicGeometry.FlatBaseChange.affine_sigmaDesc_fpqc`: for a flat affine cover `𝒱` of `S` with finitely many members (and its index type `Small.{u}`), the map `Sigma.desc 𝒱.cover.f` from the coproduct of the members to `S` is flat, surjective and quasi-compact. The coproduct is affine, as a finite coproduct of affine schemes.

## Watch for

- The module docstring announces that finite type of a quasi-coherent module descends along fpqc coverings (Tag 05AZ), with its affine case and locality on an open cover. The file holds none of these, only the two results above; its sections on them are empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/FlatBaseChange/Descent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 2 are kept. The 12 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
