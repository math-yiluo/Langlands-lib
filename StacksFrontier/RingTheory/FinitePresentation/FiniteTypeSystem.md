# Directed systems of finite-type models

Module `StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file constructs a directed system of base changes of an algebra over a subring. Its base stages exhaust the ambient ring, and each transition between model algebras is a base change.

In `Algebra.FiniteTypeSystem`, `Index` orders the finite-type ℤ-subalgebras of a commutative ring `R` that contain a fixed subring `R₀`. For an index `i`, `Base` is the corresponding ring `R_i` and `Ring` is `R_i ⊗[R₀] S₀` for a commutative `R₀`-algebra `S₀`. The transitions `baseMap` and `ringMap` are inclusion and its tensor with the identity. The cocone maps are `baseToRing` and `ringToRing`.

- `base_jointly_surjective` covers `R` by the `R_i` when `R₀` is of finite type over ℤ.
- `ring_colimit` assumes that same finiteness and a compatible pushout `S ≅ R ⊗[R₀] S₀`. Every element of `S` has a stage representative and two elements at a stage with equal images in `S` become equal at a later stage.
- `ringMap_isPushout` gives the base-change square for `i ≤ j`. Under the pushout description of `S`, `ringToRing_isPushout` gives the analogous square from each stage to `S`.

The construction adjoins each needed element of `R` to a finite-type stage, then transports the module-colimit result for tensor products along the pushout isomorphism. The colimit and pushout statements allow an arbitrary commutative `R₀`-algebra `S₀`. The instances making the stages finite type over their bases require finite type of `S₀` over `R₀`.

[Tag 00R1](https://stacks.math.columbia.edu/tag/00R1).

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FinitePresentation/FiniteTypeSystem.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 42 declarations of the source file 40 are kept. The 2 left out are not needed by the results for which the extract is made: `Algebra.FiniteTypeSystem.algebraMap_base_injective`, `Algebra.FiniteTypeSystem.instIsScalarTowerRing_1`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
