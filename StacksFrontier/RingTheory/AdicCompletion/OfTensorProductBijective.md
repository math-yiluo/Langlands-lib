# Completion as a tensor product for finite modules

Module `StacksFrontier.RingTheory.AdicCompletion.OfTensorProductBijective`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite module over a commutative Noetherian ring, adic completion is obtained by extending scalars to the completed ring.

`AdicCompletion.bijective_ofTensorProduct` proves that for any ideal I of R and any finite R-module M, the canonical map from the tensor product over R of the I-adic completion of R with M to the I-adic completion of M is bijective.

The proof presents M as a quotient of a finite free module. It applies Mathlib’s comparison to that quotient, which lives in the universe of R, and transports the result by naturality along the linear isomorphism with M. The universe of M can be chosen independently of that of R.

EGA 0 7.7.8, in the case of base change to the completed ring.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 7.7.8 | `bijective_ofTensorProduct` | B = Â |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/OfTensorProductBijective.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
