# Normality of the normalization

Module `StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves normality of the normalization and describes its behavior on generic points.

## Normalization

For a scheme X whose quasi-compact opens have finitely many irreducible components (the witness `hX`),
`Scheme.isNormal_normalizationScheme` gives a normal normalization `X.normalizationScheme hX`, and
`Scheme.isNormal_normalizationScheme_of_isReduced` is the reduced case.
`Scheme.normalization_mem_genericPoints` shows that the normalization morphism
`X.stacksNormalization hX` sends generic points of irreducible components to generic points of
irreducible components; `Scheme.normalization_mem_genericPoints_of_isReduced` is the reduced case.
Along the way, `isNormal_spec_of_isNormalRing` shows that the spectrum of a normal ring is normal.

The proofs pass to the reduction of X. On a reduced affine chart the normalization
is the spectrum of the integral closure in the total ring of fractions.
`mem_genericPoints_of_forall_comap_minimalPrimes` shows that any morphism f : Z ⟶ X sends
generic points of irreducible components to generic points of irreducible components when
every point of Z lies in an affine open V inside the preimage of an affine open U of X such
that every minimal prime of Γ(Z, V) contracts to a minimal prime of Γ(X, U).
`comap_mem_minimalPrimes_of_map_nonZeroDivisors` uses prime avoidance to show that a map
of reduced rings preserving non-zerodivisors contracts minimal primes to minimal primes when
the source has finitely many minimal primes. Here the non-zerodivisors become units in the
total ring of fractions (`isUnit_app_fromGenericPointResidueFields`), hence stay
non-zerodivisors in the relative normalization over an affine open
(`fromNormalization_app_mem_nonZeroDivisors`). The general case is transported from the reduced
one by `mem_genericPoints_of_iso` and `mem_genericPoints_subschemeι_nilradical`, the closed
immersion of the reduction being a homeomorphism.

The module docstring also announces that the normalization morphism is an isomorphism exactly
when X is normal, and the preservation of normality under a separable extension of the ground
field; they are not in this file.

The normality theorem is the normality half of Tag 035Q part (1). The generic-point
result supplies the mapping condition of Tag 035Q part (4). The normalization results cite
EGA II 6.3.8 and II 6.3.6 in partial or special cases.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.3.8 | `isNormal_normalizationScheme_of_isReduced` | partial |
| EGA | II 6.3.6 | `isNormal_normalizationScheme` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/Normal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 11 are kept. The 3 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.isIso_normalization_iff_isNormal`, `AlgebraicGeometry.Scheme.isIso_normalization_of_isNormal`, `AlgebraicGeometry.isNormal_pullback_of_isSeparableExtension`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
