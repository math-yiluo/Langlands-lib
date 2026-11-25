# Finite presentation and freeness after localization

Module `StacksFrontier.RingTheory.FinitePresentation.FreeAway`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a map of commutative rings `R → S`, an `S`-module `M`, and an element `f ∈ R`, this file packages the four localized conditions used in generic freeness and proves that they are independent of the localization models.

`Algebra.IsFinitePresentationFreeAway R S M f` says that `S_f` is finitely presented as an `R_f`-algebra, `M_f` is finitely presented as an `S_f`-module, and both `S_f` and `M_f` are free as `R_f`-modules. The definition uses `Localization.Away f` for `R_f`, the localization of `S` at the image of the powers of `f` for `S_f`, and the tensor product `S_f ⊗[S] M` for `M_f`.

`Algebra.isFinitePresentationFreeAway_iff` tests the predicate on any alternative models of the three localizations. It takes the corresponding ring localization structures, a map `l : M →ₗ[S] Mf` exhibiting the module localization, and compatible scalar towers. In particular, the action of `Rf` on `Mf` is the restriction of the `Sf`-action.

The proof uses uniqueness of the localization isomorphisms and extends scalars on the module isomorphism to check semilinearity. Finite presentation and freeness then transport across the isomorphisms.

The input `f` may be zero. The separate generic freeness result cited as Tag 051T supplies a suitable nonzero element under its finiteness and domain hypotheses.

[Tag 051U](https://stacks.math.columbia.edu/tag/051U).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [051U](https://stacks.math.columbia.edu/tag/051U) | `IsFinitePresentationFreeAway` | The condition of the source's display, as a predicate on `f`, with the canonical models of the localizations; `M_f` is the base change `S_f ⊗[S] M`. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FinitePresentation/FreeAway.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
