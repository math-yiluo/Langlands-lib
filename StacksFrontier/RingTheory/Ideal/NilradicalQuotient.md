# The nilradical under a ring isomorphism

Module `StacksFrontier.RingTheory.Ideal.NilradicalQuotient`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let R and S be commutative rings and e : R ≃+* S a ring isomorphism. The file shows that e carries the nilradical onto the nilradical and so induces an isomorphism of the reductions.

- `Ideal.map_nilradical`: the image of `nilradical R` under e is `nilradical S`. It is `Ideal.map_radical_of_surjective` at the zero ideal.
- `RingEquiv.quotientNilradical`: the isomorphism R ⧸ nilradical R ≃+* S ⧸ nilradical S induced by e, built with `Ideal.quotientEquiv`. The simp lemma `RingEquiv.quotientNilradical_mk` says that it takes the class of x to the class of e x; this holds by definition.

The module docstring describes the spectrum of a quotient by an ideal of nilpotents, the heights of its primes and minimal primes over its ideals; none of those results is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Ideal/NilradicalQuotient.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 3 are kept. The 9 left out are not needed by the results for which the extract is made: `Ideal.exists_mem_minimalPrimes_map_quotientMk_height_eq`, `Ideal.height_comap_quotientMk_of_le_nilradical`, `Ideal.le_height_of_mem_minimalPrimes_map_quotientMk`, `Ideal.mem_minimalPrimes_comap_quotientMk_of_le_nilradical`, `Ideal.minimalPrimes_map_quotientMk_of_le_nilradical`, `Ideal.minimalPrimes_sup_of_le_nilradical`, `Ideal.radical_sup_of_le_nilradical`, `PrimeSpectrum.comapQuotientMkOrderIso`, `PrimeSpectrum.comapQuotientMkOrderIso_apply`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
