# Bounds and finiteness for ideal depth

Module `StacksFrontier.RingTheory.Depth.Dimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file bounds the depth of a finite module along an ideal by the Krull dimension of its support and proves finiteness over Noetherian rings.

`Module.depth_le_supportDim` assumes a finite module M over a commutative ring R and an ideal I with IM ≠ M. It bounds the I-depth of M by dim Supp(M). `Module.depth_le_ringKrullDim` specializes to the maximal-ideal depth of a commutative local ring as a module over itself. `Module.depth_lt_top` proves finite I-depth for the same finite-module and ideal hypotheses when R is Noetherian.

For the dimension bound, each nonzerodivisor avoids the minimal primes of the annihilator of the relevant quotient. Induction over a regular sequence then shows that the support dimension decreases by at least its length. The final quotient is nonzero and has support of dimension at least zero. For finiteness, a prime in Supp(M/IM) supplies a fixed upper endpoint for chains of primes in the successive supports. Each sequence length is bounded by the height of that prime, finite by Krull’s height theorem.

The comparison with support dimension takes place in `WithBot ℕ∞`, where empty support has dimension ⊥. The support bound works over arbitrary commutative rings, with the ideal hypothesis ensuring that depth uses the regular-sequence supremum. The finiteness argument needs the finite height of a single prime even when the ring has infinite Krull dimension.

References include Tag 00LK, Tag 0AUJ, EGA 0 16.4.5 (16.4.5.1), and EGA IV 5.7.3 for the structure sheaf case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00LK](https://stacks.math.columbia.edu/tag/00LK) | `depth_le_supportDim` |  |
| [0AUJ](https://stacks.math.columbia.edu/tag/0AUJ) | `depth_lt_top` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.4.5 | `depth_le_supportDim` | (16.4.5.1) |
| EGA | IV 5.7.3 | `depth_le_ringKrullDim` | F = O_X |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/Dimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
