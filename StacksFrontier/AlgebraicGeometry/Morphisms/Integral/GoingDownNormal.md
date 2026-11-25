# Going down for integral morphisms of normal schemes

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GoingDownNormal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An integral morphism between normal locally Noetherian schemes lifts generalizations when it sends generic points of irreducible components to generic points of irreducible components.

`generalizingMap_base_of_isIntegralHom_of_isNormal` takes such a morphism f : X ⟶ Y and the generic-point hypothesis `hgen`. It proves `GeneralizingMap f.base`, so each generalization of f(x) lifts to a generalization of x. Both X and Y carry the local Noetherianity and normality assumptions.

The proof takes a normal integral affine neighborhood of f(x) and the open-and-closed integral component of its preimage containing x. This component is integral over the affine neighborhood and hence affine. The generic-point hypothesis gives dominance on this pair, so the affine section map is an injective integral extension of domains with integrally closed base. Mathlib’s going-down theorem then gives the desired lift. The auxiliary `isClosedImmersion_sigma_ι` shows that a summand of a coproduct of schemes maps in by a closed immersion.

References are Stacks Project Tag 09IL, Tag 0GLQ and Tag 037F.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Integral/GoingDownNormal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
