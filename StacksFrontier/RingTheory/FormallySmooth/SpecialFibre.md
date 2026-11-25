# Adic formal smoothness from the special fibre

Module `StacksFrontier.RingTheory.FormallySmooth.SpecialFibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a flat local map of Noetherian local rings, adic formal smoothness on the special fibre implies adic formal smoothness of the original map.

`RingHom.FormallySmoothNAdic.of_flat_of_specialFibre` takes a local homomorphism A → B with B flat over A and both rings Noetherian local. Write k for the residue field of A and B̄ for the base change of B to k. If k → B̄ is formally smooth for the maximal-ideal-adic topology of B̄, then A → B is formally smooth for the maximal-ideal-adic topology of B.

`RingHom.FormallySmoothNAdic.of_algEquiv` transports the maximal-ideal-adic property along a base-algebra isomorphism of local target rings. `RingHom.formallySmoothNAdic_bot_iff` identifies the zero-ideal condition with `Algebra.FormallySmooth`. `RingHom.section_of_disjoint` constructs a section of a surjection from a compatible map into a quotient by an ideal meeting the kernel trivially.

A lifting problem whose base map kills the maximal ideal of A factors through the special fibre. The proof uses a fibre product, Artin–Rees and flatness to handle a square-zero kernel annihilated by that maximal ideal, then inducts on the power annihilating a general square-zero kernel.

The hypothesis `hbar` is adic formal smoothness of the special fibre. The theorem proves direction (2) ⇒ (3) of Tag 07NQ. Both its lifting predicates and the zero-ideal comparison use test rings in the join of the corresponding source and target universes.

## References

Stacks Project, Tag 07NQ. The implication is used for discrete valuation rings in Tag 09E7. EGA 0 19.0.2 (I) and 0 19.7.1 (b ⇒ a), and SGA 1 III 1.7 for its sufficiency direction.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07NQ](https://stacks.math.columbia.edu/tag/07NQ) | `FormallySmoothNAdic.of_flat_of_specialFibre` | (2) ⟹ (3) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.0.2 | `FormallySmoothNAdic.of_flat_of_specialFibre` | I, one direction |
| EGA | 0 19.7.1 | `FormallySmoothNAdic.of_flat_of_specialFibre` | b) ⇒ a) |
| SGA | 1 III 1.7 | `FormallySmoothNAdic.of_flat_of_specialFibre` | if direction |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/SpecialFibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
