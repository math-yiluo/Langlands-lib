# The defining pullback square of a fibre

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FibreOfOpenRestriction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on scheme-theoretic fibres.

- `AlgebraicGeometry.isPullback_fiberι_fiberToSpecResidueField`: for a morphism `f : X ⟶ Y` and a point `y` of `Y`, the square formed by the embedding of the fibre `f.fiberι y` into `X`, the map `f.fiberToSpecResidueField y` to `Spec κ(y)`, `f`, and `Y.fromSpecResidueField y` is a pullback (`IsPullback`), that is, `X_y = X ×_Y Spec κ(y)`. It is `IsPullback.of_hasPullback`, the fibre being defined as this pullback.

## Watch for

- The module docstring announces the identification of the fibre of the restriction of `f` to an open `U` of `X` with the trace of `U` on the fibre of `f`, and its use for geometric irreducibility (Tag 0559). The file holds none of this, only the square above; the variable `U` it declares is not used.

## References

EGA III 4.7.1, EGA IV 11.2.8 in part, and EGA IV 9.4.1, as in the table below.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | III 4.7.1 | `isPullback_fiberι_fiberToSpecResidueField` | X_y = X ×_Y Spec(κ(y)) |
| EGA | IV 11.2.8 | `isPullback_fiberι_fiberToSpecResidueField` | partial |
| EGA | IV 9.4.1 | `isPullback_fiberι_fiberToSpecResidueField` | X_s = X ×_S Spec κ(s) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/GenericFibre/FibreOfOpenRestriction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 1 are kept. The 8 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.fiberOpensIso`, `AlgebraicGeometry.fiberOpensIso_hom_fiberToSpecResidueField`, `AlgebraicGeometry.fiberOpensIso_hom_fiberToSpecResidueField_assoc`, `AlgebraicGeometry.fiberOpensIso_hom_fiberι`, `AlgebraicGeometry.fiberOpensIso_hom_fiberι_assoc`, `AlgebraicGeometry.geometricallyIrreducible_fiberToSpecResidueField_of_dense_opens_comp`, `AlgebraicGeometry.geometricallyIrreducible_opens_fiber_iff`, `AlgebraicGeometry.isPullback_fiberToSpecResidueField_comp_opens`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
