# Composition and identity for module pullbacks

Module `StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Pullback of module sheaves along a morphism of ringed spaces is defined by adjunction to pushforward. This file constructs the canonical identity and composition isomorphisms.

## Isomorphisms

- `Stacks.PullbackPseudofunctor.idAdjunction X` is the identity adjunction, read as an adjunction between the identity functor and pushforward along `𝟙 X`. `modulePullbackIdIso` identifies pullback along the identity with the identity functor.
- For f : X′ ⟶ X and g : X″ ⟶ X′, `compAdjunction f g` composes the adjunctions of f and g, its right adjoint read as pushforward along g ≫ f. `modulePullbackCompIso` identifies pullback along g ≫ f with pulling back first along f, then along g.

The isomorphisms follow from uniqueness of left adjoints: in each case the two functors compared are left adjoint to the same pushforward, since pushforward along an identity is the identity functor and pushforward along g ≫ f is the composite of the two pushforwards, both by definition.

The statements use `RingedSpace.{u,u}` and the module functors over `structureSheafRing`. The file states no equation for the two isomorphisms. Its module docstring lists results it does not contain: the identification of the components of `modulePullbackCompIso` with `Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison`, the invertibility of that map, the unit and counit equations and the associativity coherence. Stacks Project Tag 0097 is cited for the related construction over `ringCatSheaf`.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/PullbackPseudofunctor/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 23 declarations of the source file 4 are kept. The 19 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
