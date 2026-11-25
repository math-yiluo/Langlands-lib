# Reduced tensor products over a field

Module `StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Geometric reducedness of one factor ensures reducedness of its tensor product with a reduced algebra over a field. Separable and separably generated field extensions are geometrically reduced.

- `Algebra.IsGeometricallyReduced.isReduced_tensorProduct` gives an instance of reducedness for R ⊗ₖ S when R is a reduced commutative k-algebra and S is a geometrically reduced commutative k-algebra.
- `Algebra.IsGeometricallyReduced.of_isSeparable` proves geometric reducedness of separable algebraic field extensions. `Stacks.GeometricallyReduced.Separability.isGeometricallyReduced_of_isSeparablyGenerated` does so for separably generated field extensions.
- `Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated` proves that K ⊗ₖ S is reduced when S is reduced and K/k is separable or separably generated in the sense of the hypothesis below.

The tensor product instance reduces R to finitely generated subalgebras and embeds those into finite products of fraction fields of their minimal-prime quotients. The separably generated case passes through a separating transcendence basis to a rational function field and a separable algebraic extension; a separable algebraic extension is tested on its subextensions of finite type, which are formally unramified.

The disjunctive hypothesis uses the library’s `Algebra.StacksIsSeparableExtension` and Mathlib’s `Algebra.IsSeparablyGenerated`, allowing transcendental extensions. The theorem named `of_isSeparable` uses Mathlib’s separable algebraic condition. The module docstring also announces results over a perfect field (Tag 00I4) and the fact that a separable extension base changed to a purely inseparable one is a field; they are not in this file, and the section on reduced algebras over a perfect field is empty.

The tensor product instance is Tag 034N. The disjunctive separability statement is Tag 030U, using the notions of Tag 030O. Related references are EGA 0 23.1.7, EGA IV 4.3.5, EGA IV 4.3.6 and EGA IV 6.7.6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [034N](https://stacks.math.columbia.edu/tag/034N) | `Algebra.IsGeometricallyReduced.isReduced_tensorProduct` | Stated with Mathlib's `Algebra.IsGeometricallyReduced` in place of the source's   Definition 030S, the two being equivalent by Lemma 030V; as an instance, since both hypotheses   are classes. |
| [030U](https://stacks.math.columbia.edu/tag/030U) | `Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated` | Stated with the two notions of Definition 030O as a disjunctive hypothesis, as in   the source: separably generated implies separable is Lemma 030X, whose proof uses this lemma. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 6.7.6 | `isGeometricallyReduced_of_essFiniteType` | special case |
| EGA | 0 23.1.7 | `Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated` | partial |
| EGA | IV 4.3.5 | `Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated` | more general |
| EGA | IV 4.3.6 | `Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/GeometricallyReduced/TensorProduct.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 10 are kept. The 4 left out are not needed by the results for which the extract is made: `Algebra.IsGeometricallyReduced.of_perfectField`, `PerfectField.isReduced_tensorProduct`, `PerfectField.isReduced_tensorProduct_field`, `Stacks.GeometricallyReduced.Separability.isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above; the source's fifth belongs to a declaration left out.
