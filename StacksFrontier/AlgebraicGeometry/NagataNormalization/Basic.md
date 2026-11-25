# Finite normalization over a Nagata base

Module `StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves finiteness of relative normalization over a Nagata base under hypotheses on the source and its generic residue fields, and applies the result to the normalization of a Nagata scheme.

`AlgebraicGeometry.isFinite_fromNormalization` applies to a quasi-compact, quasi-separated morphism `f : X ⟶ S` with `S` Nagata and `X` reduced. Each quasi-compact open of `X` must have finitely many irreducible components, and at each generic point of `X` the residue field must be finitely generated over the residue field of its image. Under these hypotheses, Mathlib’s relative normalization map `f.fromNormalization` is finite. The criterion behind it, `isFinite_fromNormalization_of_module_finite`, gives finiteness of `f.fromNormalization` once the integral closure of `Γ(S, U)` in `Γ(X, f⁻¹U)` is a finite module for every affine open `U` of `S`.

`Scheme.isFinite_normalization` proves finiteness of the normalization `X.stacksNormalization hX` of a Nagata scheme `X`, with an explicit component-finiteness witness `hX` for quasi-compact opens used to form the normalization map.

For relative normalization, the proof checks module finiteness of the integral closure on affine opens of `S`. Reducedness makes evaluation at the finitely many generic points of the preimage injective. The integral closure embeds in the product of the integral closures in their residue fields, which are finite modules over the Noetherian base section ring. For ordinary normalization the proof uses the map from the spectra of the generic residue fields, whose surjectivity on stalks supplies the residue-field condition.

`IsNagataScheme` is StacksFrontier’s own predicate and not a class, so it enters the statements as an explicit hypothesis. The witness `hX` follows from the Nagata condition, but this file does not derive it: the module docstring and the docstring of `Scheme.isFinite_normalization` refer to a form without the witness, and the module docstring also announces a finite type case and results over a field; none of these is in this file.

The relative criterion is Tag 0AVK.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0AVK](https://stacks.math.columbia.edu/tag/0AVK) | `isFinite_fromNormalization` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NagataNormalization/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 6 are kept. The 4 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.isFinite_normalization_of_isNagataScheme`, `AlgebraicGeometry.isDominant_normalizationOverField`, `AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType`, `AlgebraicGeometry.isFinite_normalizationOverField`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
