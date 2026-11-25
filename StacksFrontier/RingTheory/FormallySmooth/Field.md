# Formal smoothness and separability of field extensions

Module `StacksFrontier.RingTheory.FormallySmooth.Field`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Formal smoothness of K over a field k is equivalent to separability of the field extension K/k, including transcendental extensions.

`Algebra.FormallySmooth.of_algebraicIndependent_and_of_isSeparable_and_of_isSeparableExtension` proves formal smoothness for purely transcendental, separable algebraic, and separable extensions. The purely transcendental clause takes an algebraically independent set that generates K as a field over k. `Algebra.FormallySmooth.isSeparableExtension` gives necessity, and `Algebra.FormallySmooth.iff_isSeparableExtension` combines both directions.

`Algebra.isSeparableExtension_of_charZero_and_tfae` proves separability in characteristic zero and shows that the following six conditions are equivalent in every characteristic.

- Separability over k.
- Reducedness after tensoring over k with `AdjoinPthRoots k`.
- Geometric reducedness over k.
- Injectivity of the map from the base change of Ω(k/ℤ) to Ω(K/ℤ).
- Vanishing of `Algebra.H1Cotangent k K`.
- Formal smoothness over k.

`Stacks.FormallySmooth.SeparableTFAE.isGeometricallyReduced_of_isSeparableExtension` proves on its own that a separable extension K/k is geometrically reduced over k.

`Algebra.formallySmooth_of_perfectField` gives formal smoothness for every extension of a perfect field.

Sufficiency reduces the cotangent calculation for each polynomial relation to a finitely generated subextension with a separating transcendence basis, and necessity uses a retraction of the differential map over ℤ. Reducedness after the root base change forces p-th powers to preserve linear independence, giving separating transcendence bases in positive characteristic.

`Algebra.StacksIsSeparableExtension` requires a separating transcendence basis in each finitely generated subextension; the docstrings and the notes of the Stacks attributes, quoted in the table below, write its name without the prefix `Stacks`. `Algebra.IsSeparable` is the separable algebraic predicate. The root test uses the exponential characteristic p, which equals 1 in characteristic zero. The module docstring also lists a statement for characteristic zero and characteristic p > 0 (Tag 0321) that is not in this file.

## References

Stacks Project, Tag 0320, Tag 031Y, and Tag 0322. The definition of separability refers to Tag 030O. EGA 0 19.0.2, 0 19.6.1, 0 19.10.3, 0 20.6.3, 0 21.5.1, 0 22.2.1, IV 4.3.5, and IV 4.3.9, and SGA 1 III 1.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0320](https://stacks.math.columbia.edu/tag/0320) | `Algebra.FormallySmooth.of_algebraicIndependent_and_of_isSeparable_and_of_isSeparableExtension` | The source's parts (1), (2), (3) are the conjuncts `.1`, `.2.1`, `.2.2`. Purely transcendental is `AlgebraicIndependent` together with `IntermediateField.adjoin k s = ⊤`, as in the Mathlib sibling `Algebra.FormallySmooth.of_algebraicIndependent`; separable algebraic is `Algebra.IsSeparable`; separable is `Algebra.IsSeparableExtension`, Definition 030O(2), which does not presuppose algebraicity. See the module docstring. |
| [031Y](https://stacks.math.columbia.edu/tag/031Y) | `Algebra.FormallySmooth.isSeparableExtension` | Separability is `Algebra.IsSeparableExtension` (Definition 030O(2)), not Mathlib's `Algebra.IsSeparable`, which asks the extension to be algebraic and would make the statement false for purely transcendental extensions. See the module docstring. |
| [0322](https://stacks.math.columbia.edu/tag/0322) | `Algebra.isSeparableExtension_of_charZero_and_tfae` | The equivalences are stated uniformly in the characteristic: `k^{1/p}` is `AdjoinPthRoots k` for the exponential characteristic, which in characteristic zero makes the second condition, hence all of them, automatic, and the source's characteristic-zero list is recovered. Differentials are taken over `𝐙` in both characteristics. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.0.2 | `formallySmooth_of_isSeparablyGenerated` | II, special case |
| EGA | 0 19.6.1 | `formallySmooth_of_isSeparablyGenerated` | special case |
| EGA | 0 21.5.1 | `formallySmooth_of_isSeparablyGenerated` | special case |
| EGA | 0 22.2.1 | `formallySmooth_of_isSeparablyGenerated` | special case |
| EGA | 0 19.6.1 | `Algebra.FormallySmooth.of_algebraicIndependent_and_of_isSeparable_and_of_isSeparableExtension` | sufficiency |
| EGA | 0 21.5.1 | `Algebra.FormallySmooth.of_algebraicIndependent_and_of_isSeparable_and_of_isSeparableExtension` | more general |
| EGA | 0 21.5.1 | `Algebra.FormallySmooth.of_algebraicIndependent_and_of_isSeparable_and_of_isSeparableExtension` | more general |
| EGA | 0 19.0.2 | `Algebra.FormallySmooth.of_algebraicIndependent_and_of_isSeparable_and_of_isSeparableExtension` | sufficiency |
| EGA | 0 22.2.1 | `Algebra.FormallySmooth.of_algebraicIndependent_and_of_isSeparable_and_of_isSeparableExtension` | special case |
| EGA | 0 19.6.1 | `Algebra.FormallySmooth.isSeparableExtension` | necessity |
| EGA | 0 19.0.2 | `Algebra.FormallySmooth.isSeparableExtension` | necessity |
| EGA | 0 19.6.1 | `Algebra.FormallySmooth.iff_isSeparableExtension` |  |
| EGA | 0 21.5.1 | `Algebra.FormallySmooth.iff_isSeparableExtension` | more general |
| EGA | 0 19.0.2 | `Algebra.FormallySmooth.iff_isSeparableExtension` |  |
| EGA | IV 4.3.9 | `isDomain_tensorProduct_fractionRing_mvPolynomial` | special case |
| EGA | IV 4.3.5 | `isSeparableExtension_of_isReduced_tensorProduct_adjoinPthRoots` | special case |
| EGA | 0 20.6.3 | `Algebra.isSeparableExtension_of_charZero_and_tfae` |  |
| EGA | 0 19.0.2 | `Algebra.formallySmooth_of_perfectField` | special case |
| EGA | 0 19.10.3 | `Algebra.formallySmooth_of_perfectField` | perfect base field |
| EGA | 0 19.6.1 | `Algebra.formallySmooth_of_perfectField` | special case |
| EGA | 0 21.5.1 | `Algebra.formallySmooth_of_perfectField` | special case |
| EGA | 0 22.2.1 | `Algebra.formallySmooth_of_perfectField` | more general |
| SGA | 1 III 1.2 | `Algebra.formallySmooth_of_perfectField` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/Field.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 32 declarations of the source file 30 are kept. The 2 left out are not needed by the results for which the extract is made: `Algebra.FormallySmooth.of_charZero_and_iff_isSeparableExtension_of_charP`, `Stacks.FormallySmooth.CharacterizeSeparable.solution`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 23 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
