# Reciprocity for cyclic totally ramified extensions

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.Conclusion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a compact, Hausdorff, totally disconnected group `G`, with degree map `D`, module `A` and valuation `v`, this file proves that the reciprocity homomorphism `finiteReciprocityHom` is bijective for a finite cyclic totally ramified extension L/K of a finite abstract field `K : FiniteAbstractField G` (`E : FiniteCyclicSubextension K` with `hTot : E.IsTotallyRamified D`). All three results assume the class field axiom `hcf`; the last two also take `hAxiom : v.SatisfiesUnramifiedUnitCohomology D`.

## Results

- `abstractReciprocity_cyclicTotallyRamified_exponent_eq_zero`: let σ be the chosen Frobenius lift of degree one attached to a generator, Σ its fixed field, π_Σ ∈ A_Σ and π_L a prime element of L, and k a natural number with k < [L : K]. If k π_L + w and k π_Σ have the same norm to K for a unit w of L, then k = 0.
- `abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_injective`: the reciprocity homomorphism has trivial kernel.
- `abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective`: it is bijective.

## Proofs

For the exponent, the fixed element of valuation k built in `abstractReciprocity_cyclicTotallyRamified_fixedSource` is fed to the valuation argument `abstractReciprocity_totallyRamified_valuation_forces_exponent_zero` for an auxiliary totally ramified extension. For injectivity, an element of the kernel is written as the k-th power of the generator; reciprocity sends it to k times the class of the norm of π_Σ from Σ to K, Σ/K has residue degree one, and `primeNormClass_eq_zero_exists_unit_norm_eq` gives the norm equation, so k = 0. Bijectivity follows from injectivity and equality of cardinalities (`cyclicReciprocity_card_equality`), the norm quotient being finite under the class field axiom.

## Points to watch

The chosen prime elements of `v` (`chosenPrimeElement`) and the chosen Frobenius lift enter the proofs; the results are stated for the library's own abstract fields and cyclic subextensions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/Conclusion.lean`: the Lean file is the source byte for byte (SHA-256 `a29017700b41f4809dd261ba3eb2dd74953dc6a3f3180aadaa0769549cc57481`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
