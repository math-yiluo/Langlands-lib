# Filtered colimits of essentially finitely presented local maps

Module `StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation.BaseChangeLocalization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves a colimit presentation for a local homomorphism `φ : R →+* S` of commutative local rings when `S` is a localization of a finitely presented `R`-algebra. The system has prime-localization transition maps after base change.

## Main results

- `descent_core` and `Descent.systemBundle` take explicit data: a finitely presented intermediate algebra `T` and a submonoid at which `S` localizes `T`, with the original map agreeing with the algebra map. They give a nonempty directed preorder of local maps `ψᵢ : Rᵢ → Sᵢ` with commuting squares and local transitions, whose colimit recovers `φ` via ring isomorphisms on both sides. Each `Rᵢ` is essentially of finite type over ℤ, and each `ψᵢ` is essentially of finite type. For every `i ≤ j`, the canonical map from the tensor product of `Sᵢ` and `Rⱼ` over `Rᵢ` to `Sⱼ` exhibits `Sⱼ` as the localization at a prime of that tensor product.
- `Descent.descendSystemPointed` builds the `S`-side of such a system over an index with a least element, given the base system and relations of `T` descended to that element.

The proof writes the base as a colimit of local models over ℤ, descends a finite polynomial presentation of `T` to one stage, and restricts to the cofinal tail there. The quotient-colimit and localization-colimit results recover `S`, while base change of the quotient followed by successive localizations gives the transition property.

The auxiliary result `Descent.cond4_fromBaseChange` takes the compatible quotient base-change isomorphism as the hypothesis `hbc`. `Descent.cond4_baseChange` supplies it using the quotient base-change theorem and `hfT`, which pins the quotient transitions to the canonical coefficient maps. The pointed construction `Descent.descendSPointedBundle` assumes the quotient-colimit data `eT` and `heT` identifying the colimit with `T` via the specified stage maps. `descent_core` packages these steps and uses one universe for its rings and index.

The module docstring and the docstring of `descent_core` still refer to the Tag 00QV theorem for essentially finitely presented maps and to a comparison of finiteness predicates; neither is in the file.

## References

The base-ring presentation comes from Tag 00QT. The table of references below cites SGA 3 X 4.4.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 X 4.4 | `systemBundle` | Proof step b) |
| SGA | 3 X 4.4 | `descent_core` | Proof step b) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/EssentialFiniteness/ColimitFinitePresentation/BaseChangeLocalization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 6 are kept. The 4 left out are not needed by the results for which the extract is made: `Stacks.EssentialFiniteness.ColimitPresentation.main_theorem_00qv`, `descent_of_finitePresentation`, `essFinitePresentation_essFiniteType`, `finitePresentation_essFinitePresentation`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
