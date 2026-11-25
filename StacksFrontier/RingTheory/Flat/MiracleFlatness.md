# Miracle flatness

Module `StacksFrontier.RingTheory.Flat.MiracleFlatness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves flatness of a local ring homomorphism from the dimensions of the two rings and the closed fibre, under regularity and Cohen–Macaulay hypotheses.

For a local homomorphism R → S from a regular local ring to a Noetherian local ring, `Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add` assumes that S is Cohen–Macaulay and dim S = dim R + dim(S/𝔪ᵣS), where 𝔪ᵣ is the maximal ideal of R. It concludes that S is flat over R. The proof is also exposed as `Stacks.Flatness.MiracleFlatness.solution`.

The private `flat_of_isWeaklyRegular_of_ofList_eq_maximalIdeal` gives flatness for any local map of Noetherian local rings equipped with a generating list of 𝔪ᵣ that is weakly regular on S.

The Cohen–Macaulay dimension criterion makes the images of a minimal generating list of 𝔪ᵣ a regular sequence. Induction cuts by the first element x, which acts injectively on S, so the principal-ideal criterion lifts flatness from S/xS over R/xR. The empty list makes R a field, and a quotient equivalence identifies the ring fibre with the module quotient used in the lifting step.

The theorem uses `IsRegularLocalRing R` and, as hypothesis `hS`, the Stacks library's own predicate `Module.IsMaximalCohenMacaulay S S`, the latter expressing equality of depth at the maximal ideal of S and Krull dimension. The dimensions in the formula are `ringKrullDim` values in `WithBot ℕ∞`.

The main result is Tag 00R4. The proof uses Tag 02JN for the sequence and Tag 00ML for each lifting step. The related references are EGA IV 6.1.5 (case M = B) and IV 15.4.2 (partial e′ ⇒ b).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00R4](https://stacks.math.columbia.edu/tag/00R4) | `Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add` | Regularity of the Noetherian local ring `R` is `IsRegularLocalRing R`; Cohen-Macaulayness of `S` (Definition 00N8) is `Module.IsMaximalCohenMacaulay S S`, i.e. `depth_{𝔪_S}(S) = dim S`; and `dim(S/𝔪_R S)` is the Krull dimension of the quotient of `S` by the image ideal of the maximal ideal of `R`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 6.1.5 | `Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add` | case M = B |
| EGA | IV 15.4.2 | `Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add` | e′)⇒b), partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/MiracleFlatness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
