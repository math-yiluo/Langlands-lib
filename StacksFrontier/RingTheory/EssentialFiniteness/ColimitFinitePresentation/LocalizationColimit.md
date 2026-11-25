# Localizing the stages of a finite presentation

Module `StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation.LocalizationColimit`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file constructs the local rings in a colimit presentation of a local algebra. It starts with a directed system of local base rings and their polynomial quotients `Tᵢ`, defined by transporting a fixed finite list of relations from a least index.

## Localization and base change

- For a prime `q` of `T` and structure maps `πT i : Tᵢ → T`, `Descent.qcon` contracts `q` to `Tᵢ` and `Descent.Sobj'` localizes there. Given quotient transitions compatible with `πT`, `Descent.fSmap` induces local transitions between these localizations. The maps `Descent.psiS` from the base stages are essentially of finite type. They are local when `S` is the localization of `T` at `q`, the structure maps to the base limit and the original algebra map are local, and the quotient squares commute.
- `Descent.colimLocalization` assumes `S` is the localization of `T` at `q`, with compatible directed systems and structural maps on the base and quotient sides. It gives a ring isomorphism from the direct limit of the localized stages to `S`. Under this isomorphism and the base colimit isomorphism, the induced map of direct limits is the given local algebra map.
- `Descent.baseChangeQuotient` identifies the tensor product of `Tᵢ` with `Rⱼ` over `Rᵢ` with `Tⱼ` as an `Rᵢ`-algebra for `i ≤ j`. The two tensor-factor maps are the canonical quotient transition and coefficient map.

Surjectivity of the localization comparison lifts a numerator and denominator to a common stage, while injectivity lifts a denominator killing the numerator and moves to a later stage where the product vanishes. The base-change isomorphism uses polynomial and quotient base change, with the transported relation ideal identified by `Descent.Irel_map_eq`.

The localization theorem takes the quotient-colimit result as input. The hypotheses `eT` and `heT` identify `T` with the direct limit of the quotient stages through the specified maps `πT`. For base change, `halg` identifies the algebra map `Rᵢ → Rⱼ` with the transition map. The index and rings in these constructions use one universe.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/EssentialFiniteness/ColimitFinitePresentation/LocalizationColimit.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
