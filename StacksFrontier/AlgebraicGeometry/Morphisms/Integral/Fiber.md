# Closed points in the fibres of integral morphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An integral morphism of schemes has closed singletons in each scheme-theoretic fibre.

For f : X ⟶ S with `IsIntegralHom f` and any x in X, `isClosed_singleton_asFiber_of_isIntegral` proves that the point represented by `f.asFiber x` is closed in the fibre over f(x).

Integrality survives base change to the residue field, making the fibre the spectrum of an algebra integral over that field. The prime corresponding to x lies over the maximal ideal of the field and is therefore maximal.

Reference is Stacks Project Tag 02NT.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02NT](https://stacks.math.columbia.edu/tag/02NT) | `isClosed_singleton_asFiber_of_isIntegral` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Integral/Fiber.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
