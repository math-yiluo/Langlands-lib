# Geometric reducedness after purely inseparable base change

Module `StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedReduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a scheme locally of finite type over a field and with finitely many irreducible components, a finite purely inseparable extension of the ground field makes the reduction of the base-changed scheme geometrically reduced.

## The field extension and the reduction

`AlgebraicGeometry.exists_finite_purelyInseparable_extension_geometricallyReduced_reduction` takes f : X ⟶ Spec k with `LocallyOfFiniteType f` and `hX` asserting finitely many irreducible components. It produces a field extension k′/k with `Module.Finite k k'` and `IsPurelyInseparable k k'`, in the same universe as k and X. The resulting `GeometricallyReduced` property is for the structure morphism from the closed subscheme cut out by the vanishing ideal of the entire base change to Spec k′. Thus the reduction is taken after changing fields.

## Proof

The generic residue fields of X are essentially of finite type over k. For each, the field-theoretic construction finds a separable field model over a finite purely inseparable extension of constants. The proof embeds the constant fields in an algebraic closure of k and takes their finite compositum. The reduced tensor product of each generic residue field with the compositum embeds in a geometrically reduced algebra over the compositum, so it too is geometrically reduced.

A generic point of the reduction maps to a generic point of X, using full support of the reduction and flatness of the base-change projection. The stalk at that point of the reduced scheme is a field. The residue-field comparison identifies it over the enlarged base with the reduction of the corresponding residue-field tensor product. The generic-point criterion then gives geometric reducedness of the whole reduced scheme.

References include Tag 04KT, EGA IV 17.15.14.2, IV 4.6.6, and the first clause of IV 4.6.8.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [04KT](https://stacks.math.columbia.edu/tag/04KT) | `exists_finite_purelyInseparable_extension_geometricallyReduced_reduction` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.15.14.2 | `exists_finite_purelyInseparable_extension_geometricallyReduced_reduction` | geom. reduced reduction |
| EGA | IV 4.6.6 | `exists_finite_purelyInseparable_extension_geometricallyReduced_reduction` | more general |
| EGA | IV 4.6.8 | `exists_finite_purelyInseparable_extension_geometricallyReduced_reduction` | First clause |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Geometric/ReducedReduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
