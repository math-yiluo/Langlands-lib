# Generic points of fibres of a normalized base change

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreGenericFibrePoint`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `f : X ⟶ S` with `X` normal and locally Noetherian, `g : T ⟶ S` integral and flat, and `ν : W^ν ⟶ W` the normalization of `W = X ×_S T`, assumed locally Noetherian.

- `generalizingMap_normalization_comp_pullbackFst`: `ν ≫ pr₁ : W^ν ⟶ X` lifts generalizations (going down), since it is integral between normal schemes and sends generic points to generic points.
- `mem_genericPoints_asFiber_normalization_pullbackFst`: a point of `W^ν` that is generic in its own fibre over `S` maps to a point of `X` generic in its own fibre of `f`.

This is a step of the reduced fibre theorem (Tag 09IL). Going down comes from normality, not finiteness: a finite morphism can raise codimension.

Watch for: local Noetherianness of the normalization is a hypothesis (`hN`), not derived from the other hypotheses. The normalization also needs the hypothesis `hW` that every quasi-compact open of `W` has finitely many irreducible components. Flatness of `g` is used so that `pr₁` keeps generic points. The file also cites Tag 037F.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreGenericFibrePoint.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
