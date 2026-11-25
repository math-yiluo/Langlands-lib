# Generic points under immersions, and points of fibres

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Three results: generic points of irreducible components pull back along open and closed immersions, and a simplification for points of fibres.

- `genericPoints_preimage_of_isOpenImmersion` and `genericPoints_preimage_of_isClosedImmersion`: for an open, respectively closed, immersion `j : A ⟶ B` and a point `a` of `A`, if `j a` is generic in an irreducible component of `B`, then `a` is generic in one of `A`. The open case pulls back the component, and the closed case uses the maximality of the closure of `j a` among irreducible sets.
- `Scheme.Hom.asFiberAt_rfl` (a `simp` lemma): `asFiberAt f x (f x) rfl = f.asFiber x`. Here `Scheme.Hom.asFiberAt` (from another file) sends a point `x` of the source with `f x = y` to a point of the fibre over `y`; over `f x` itself it is `asFiber`.

## Watch for

- The module docstring announces the morphism from the fibre of a composite `i ≫ f` to the fibre of `f`, its compatibility with the inclusions of the fibres, and its immersion properties. The file holds none of these.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/FibrePoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 16 declarations of the source file 3 are kept. The 13 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
