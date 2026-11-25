# Relative dimension over a field

Module `StacksFrontier.RingTheory.RelativeDimension.FlatLocalExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a field k, a commutative k-algebra S and a prime 𝔮 of S, `IsLocalRing.relativeDimensionAt_eq_localKrullDim_of_field` shows that the relative dimension `Algebra.relativeDimensionAt k 𝔮` equals `TopologicalSpace.localKrullDim (PrimeSpectrum S)` at 𝔮, the infimum of the Krull dimensions of the open neighbourhoods of 𝔮 in Spec S. Since Spec k is a point, the fibre through 𝔮 is all of Spec S, and the proof transports the dimension at a point along the homeomorphism between that fibre and Spec S. S need not be local or of finite type.

The lemma has no docstring. The module docstring, with its reference to Stacks Tag 053T, announces the dimension formula for a flat, injective, essentially finite-type local homomorphism of local domains (closed fibre dimension plus residue transcendence degree equals transcendence degree); that formula is not in the file, whose first section heading, on domains after valuation base change, has nothing under it.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RelativeDimension/FlatLocalExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 1 are kept. The 14 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The source's 2 references to EGA and SGA, written as attributes of that library, belong to declarations left out.
