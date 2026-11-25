# Geometric reducedness at minimal primes

Module `StacksFrontier.RingTheory.Nilpotent.GeometricallyReduced`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file deduces geometric reducedness of a reduced algebra over a field from its minimal-prime localizations.

`Algebra.IsGeometricallyReduced.of_forall_minimalPrimes` takes a field k, a reduced commutative k-algebra S, and `H`, which asserts geometric reducedness over k of `Localization.AtPrime p` for every minimal prime p of S. It concludes `Algebra.IsGeometricallyReduced k S`. The field and algebra may lie in independent Lean universes.

The proof embeds S in the product of these localizations. After field extension the product of the base-changed maps is still injective. The tensor argument uses flatness and the injective comparison from tensoring a product to the product of tensors for a free module, proved by choosing a basis. Reducedness of the factors then gives reducedness of the base change.

Stacks Project Tag 07K2, using Mathlib's predicate identified with the Stacks definition by Tag 030V. SGA 3 VIB 11.7 is cited for the tensor argument in the free case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07K2](https://stacks.math.columbia.edu/tag/07K2) | `Algebra.IsGeometricallyReduced.of_forall_minimalPrimes` | Stated with Mathlib's `Algebra.IsGeometricallyReduced` in place of the source's   Definition 030S, the two being equivalent by Lemma 030V, and with the concrete localization   `Localization.AtPrime p` for the source's `S_𝔭`. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 11.7 | `injective_pi_lTensor_of_free` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nilpotent/GeometricallyReduced.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
