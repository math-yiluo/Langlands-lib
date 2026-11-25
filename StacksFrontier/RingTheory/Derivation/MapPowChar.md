# Derivations of p-th powers

Module `StacksFrontier.RingTheory.Derivation.MapPowChar`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file shows that derivations annihilate powers whose exponent is the characteristic of the algebra.

`Derivation.map_pow_char_eq_zero` takes a derivation D of a commutative R-algebra A into a module M, with R and A commutative semirings and M carrying both module structures. For any natural number p with `CharP A p` and any x in A, D(xᵖ) = 0.

The power rule gives a coefficient p acting by repeated addition. This is the scalar action by the image of p in A, which is zero by the characteristic hypothesis. This includes p = 0, where the power is x⁰.

The reference is EGA 0 21.1.5 (i).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 21.1.5 | `Derivation.map_pow_char_eq_zero` | (i) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Derivation/MapPowChar.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
