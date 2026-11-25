# The morphism from the spectrum of a residue field of `Spec R`

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueField`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on affine schemes.

- `AlgebraicGeometry.fromSpecResidueField_eq_specMap`: for a commutative ring `R` and a point `x` of `Spec R`, the canonical morphism `(Spec R).fromSpecResidueField x : Spec κ(x) ⟶ Spec R` is `Spec.map` of the structure map `R → κ(x)`, the algebra structure being `specResidueFieldAlgebra R x`. The proof goes through the isomorphism `Scheme.Spec.residueFieldIso R x` between `κ(x)` and the residue field of the prime ideal of `x`.

## Watch for

- The module docstring announces results on the residue field at the generic point of an integral scheme with geometrically integral generic fibre, and the shrinking statements of Tag 0559. The file holds none of these; its section on the fibre is empty apart from variable declarations.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/GenericFibre/GenericResidueField.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 17 declarations of the source file 1 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
