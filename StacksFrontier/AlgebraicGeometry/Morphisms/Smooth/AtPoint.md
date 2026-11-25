# Affine criterion for smoothness at a point

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A scheme morphism is smooth at a point precisely when it can be presented by a smooth ring map on suitable affine neighborhoods.

The file uses the existing predicate `InfinitesimalLifting.SmoothAt f x`, which asks for an open neighborhood of x on which the restricted morphism to the target is smooth.

`smoothAt_iff_exists_affine` equates this with the existence of affine opens U in X and V in S, with x in U and U contained in the inverse image of V, such that Γ(S, V) → Γ(X, U) is smooth.

The forward direction takes standard smooth affine opens of the smooth restriction and identifies its section maps with those of f on the corresponding opens. The converse reads smoothness of the restriction to U off the section map.

The module docstring also announces a standard smooth criterion over a prescribed affine neighbourhood of the image and the deduction of smoothness of f from smoothness at every point; neither is in the file.

Stacks Project, Tag 01V5; the module docstring also cites Tag 01V7, for the standard smooth criterion.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01V5](https://stacks.math.columbia.edu/tag/01V5) | `InfinitesimalLifting.SmoothAt` | smooth_at_point |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/AtPoint.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 1 are kept. The 6 left out are not needed by the results for which the extract is made: `InfinitesimalLifting.exists_isAffineOpen_smooth_appLE_of_smoothAt`, `InfinitesimalLifting.isIso_ι_appLE`, `InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth`, `InfinitesimalLifting.smooth_iff_forall_smoothAt`, `InfinitesimalLifting.smooth_of_forall_smoothAt`, `InfinitesimalLifting.smooth_ι_comp_of_smooth_resLE`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The one reference to EGA or SGA that the source writes as an attribute of that library belongs to a declaration left out; none remains.
