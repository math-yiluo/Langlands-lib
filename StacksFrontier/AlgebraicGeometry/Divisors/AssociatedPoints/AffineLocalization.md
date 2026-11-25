# Sections of `IsAffineOpen.fromSpec` over an affine open

Module `StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One lemma on an affine open `U` of a scheme `X`.

- `AlgebraicGeometry.fromSpec_appLE_top`: the map on sections of `hU.fromSpec : Spec Γ(X, U) ⟶ X` from `U` to the whole of `Spec Γ(X, U)` (`hU.fromSpec.appLE U ⊤ _`) is the inverse of the canonical identification `Scheme.ΓSpecIso Γ(X, U)` of `Γ(Spec Γ(X, U), ⊤)` with `Γ(X, U)`. The proof unfolds `appLE` and uses `IsAffineOpen.fromSpec_app_self`.

## Watch for

- The module docstring announces that the stalk of a quasi-coherent module at a point of an affine open is the localization of its sections there, with the definitions and lemmas for it. The file holds none of these, only the lemma above.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/AffineLocalization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 17 declarations of the source file 1 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
