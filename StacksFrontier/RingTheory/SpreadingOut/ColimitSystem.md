# Spreading out a local map and a module

Module `StacksFrontier.RingTheory.SpreadingOut.ColimitSystem`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An essentially finitely presented local homomorphism and a finitely presented module over its target can be expressed together as a directed colimit of local rings and finite modules with compatible base changes.

## Results

`RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module`, via `Stacks.SpreadingOut.LocalModuleSystem.solution`, takes a local map R → S of commutative local rings with essential finite presentation and a finitely presented S-module M. It produces a nonempty directed preorder and a system of local maps Aᵢ → Bᵢ of local rings with Bᵢ-modules Nᵢ.

- The colimits of the three diagrams are R, S and M. Their legs respect R → S and the action of S on M, and the module transition maps are semilinear.
- Each Aᵢ is essentially of finite type over ℤ and each map Aᵢ → Bᵢ is essentially of finite type. Each Nᵢ is finite over Bᵢ.
- For i ≤ j, Bⱼ is a prime localization of the pushout of Bᵢ and Aⱼ over Aᵢ. The transition on N realizes Nⱼ as base change of Nᵢ from Bᵢ to Bⱼ, expressed by `IsBaseChange`.
- The colimit legs Aᵢ → R are local, which forces the A-side transitions to be local as well.

`Stacks.SpreadingOut.LocalModuleSystem.exists_ringSystem_of_essentiallyOfFinitePresentation` constructs the ring diagrams under the same map hypotheses and also gives locality of Bᵢ → S. The supporting colimit criteria use joint surjectivity of the legs and eventual vanishing of elements in their kernels.

## Proof

The proof writes S as the localization of a finitely presented R-algebra at the contraction of S’s maximal ideal, then builds the ring system with `descent_core`. The finitely many entries of a presentation matrix for M lift to a common stage, and taking cokernels on the final tail gives the module colimit and its base-change property.

## Scope

Essential finite presentation is the library’s `RingHom.EssentiallyOfFinitePresentation` predicate. The stage conditions use Mathlib’s `EssFiniteType`. The index, rings and module are in one universe. The module diagram has its colimit in `AddCommGrpCat`.

## References

Tag 00QX for the combined system, Tag 00QM for essential finite presentation and essential finite type, and Tag 00QV for ring descent. EGA IV 1.3.10 is cited for the prime localization step and EGA 0 1.4.5 for the colimit construction.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00QX](https://stacks.math.columbia.edu/tag/00QX) | `RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module` | The system is a pair of functors `A B : Λ ⥤ CommRingCat` with a natural transformation `φ : A ⟶ B`, and a functor `N : Λ ⥤ AddCommGrpCat` with `B.obj i`-module structures compatible with the transition maps; `S_λ ⊗_{R_λ} R_μ` is the pushout in `CommRingCat` and (6) is `IsBaseChange`. Hypothesis (1) is `RingHom.EssentiallyOfFinitePresentation` (Definition 00QM (2)), Mathlib having no such predicate; (2) and (3) are Mathlib's `EssFiniteType` (Definition 00QM (1)). The conclusion also asserts that each structure map `ρ_λ : A.obj i → R` is local, which is the source's \"system of local homomorphisms of local rings\" read as a system in the category of local rings; it is realized by the construction of 00QU and is not implied by (1)–(6). See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 1.3.10 | `exists_finitePresentation_isLocalization_atPrime` | special case |
| EGA | 0 1.4.5 | `sysCocone` | more general |
| EGA | 0 1.4.5 | `sysIsColimit` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/SpreadingOut/ColimitSystem.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
