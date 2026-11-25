# The coheight of a prime and the dimension of the quotient

Module `StacksFrontier.RingTheory.Equidimensional.FlatLocal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a prime `P` of a commutative ring `R`, `coheight_eq_ringKrullDim_quotient` states that the coheight of `P` in `PrimeSpectrum R`, read in `WithBot ℕ∞`, equals the Krull dimension `ringKrullDim (R ⧸ P)`. The proof rewrites with Mathlib's `ringKrullDim_quotient` and `Order.coheight_eq_krullDim_Ici`.

The module docstring, headed by Tag 0AW4, still announces the equidimensionality of the fibres and of the base under a flat local map of Noetherian local rings, with a proof outline; the file contains none of these results.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Equidimensional/FlatLocal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 53 declarations of the source file 1 are kept. The 52 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
