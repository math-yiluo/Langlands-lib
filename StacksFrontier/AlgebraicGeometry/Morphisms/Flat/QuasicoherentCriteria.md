# Affine and local criteria for relative flatness

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of schemes f : X ⟶ S, relative flatness of a quasi-coherent module F on X can be tested by sections on affine opens or by restricting to open covers.

`isFlatOver_tfae` proves that the following four conditions are equivalent for quasi-coherent F.

1. Each stalk Fₓ is flat over the local ring of S at f(x).
2. For every pair of affine opens U in X and V in S with f(U) contained in V, the module of sections Γ(F, U) is flat over Γ(S, V).
3. There is an open cover of S and, over each member V, an open cover of f⁻¹(V) on whose members F restricts to a module flat over V.
4. There are such covers by affine opens with Γ(F, U) flat over Γ(S, V) on each pair of members U and V.

The affine argument identifies the stalk of the sheaf associated to a module M with the localization of M at the corresponding prime, compatibly with restriction of scalars in `flat_tilde_stalk_iff_localizedModule`. Flatness over the base ring is detected after localization at all maximal ideals of the source affine ring. For the cover criteria, the local rings are identified under the open immersions of U and V, point by point.

The section-module action is via the canonical map `f.appLE`. The covering families in `isFlatOver_tfae` are indexed in the common universe of the schemes and module. The module docstring also lists a result on flatness after restriction to compatible opens, which is not in the file.

Reference is Stacks Project Tag 01U4, for the characterizations.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01U4](https://stacks.math.columbia.edu/tag/01U4) | `isFlatOver_tfae` | flatness characterization |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Flat/QuasicoherentCriteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 16 declarations of the source file 15 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isFlatOver_resLE`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
