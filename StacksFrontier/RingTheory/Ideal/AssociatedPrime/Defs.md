# Associated primes of a module

Module `StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file defines the associated primes of a module M over a commutative ring R, in the sense of the Stacks project.

## Definitions

`IsAssociatedPrimeStacks R M p` requires the ideal p to be prime and to equal the annihilator of a single element m of M, written `(⊥ : Submodule R M).colon (Submodule.span R {m})`. `assStacks R M` collects these ideals, and the `simp` lemma `mem_assStacks_iff` unfolds membership.

The predicate uses equality with the annihilator itself. Mathlib’s `IsAssociatedPrime` uses equality with the radical of the annihilator. The module docstrings that follow the definitions describe associated primes on `PrimeSpectrum R`, weakly associated primes, their inclusion in the support, and associated primes over a quotient ring; none of these definitions or results is in the file.

## References

Stacks Project, Tag 00LA for associated primes. SGA 2 III 1.1 for associated primes.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00LA](https://stacks.math.columbia.edu/tag/00LA) | `IsAssociatedPrimeStacks` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 2 III 1.1 | `IsAssociatedPrimeStacks` | Ass M clause |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Ideal/AssociatedPrime/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 20 declarations of the source file 3 are kept. The 17 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
