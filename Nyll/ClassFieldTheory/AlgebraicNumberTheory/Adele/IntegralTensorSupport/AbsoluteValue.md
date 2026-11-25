# Valuation rings of completions for nonarchimedean absolute values

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file collects facts about nonarchimedean real absolute values used in the library's finite-support argument for relative ideles. It defines the valuation ring of the completion of a field at such an absolute value. It also shows that, in a finite separable extension, elements of the valuation ring of an extension completion are integral over the valuation ring of the base completion.

## Definitions and results

- `realAbsoluteValueValuation vF hvF`: a nonarchimedean absolute value vF on a field F, viewed as a valuation with values in the nonnegative reals. `realAbsoluteValueValuation_apply` gives its values.
- `absoluteValueExtension_isNonarchimedean`: any extension of a nonarchimedean absolute value along a field extension E/F is nonarchimedean. The statement has no algebraicity hypothesis.
- `absoluteValue_le_one_of_isIntegral`: if x ∈ F is integral over ℤ, then vF(x) ≤ 1 for every nonarchimedean absolute value vF on F.
- `absoluteValueCompletionIntegers vF hvF`: the valuation subring {x : ‖x‖ ≤ 1} of the completion `vF.Completion`. `mem_absoluteValueCompletionIntegers_iff` states the membership criterion.
- `isIntegral_over_baseCompletionIntegers_of_mem`: let L/K be finite and separable, vK a nonarchimedean nontrivial absolute value on K, and w an extension of vK to L. Then every element of the valuation ring of the completion of L at w is integral over the valuation ring of the completion of K at vK.

## Proofs

The ℤ-integrality bound holds because a valuation subring is integrally closed. The last theorem passes from the two absolute values on the completions to exponential valuations. The completion of K is complete, hence henselian (`henselianValuation_of_complete`). The imported `exponentialValuationSubring_eq_integralClosure_of_henselian` then identifies the valuation ring above with the integral closure of the base valuation ring. Finiteness of the completion extension comes from `completionModuleFinite` and uses nontriviality of vK.

## Points to watch

- The module comment describes the whole lattice construction: a scaling integer, a lattice in 𝓞 L, and a finite set of bad primes. This file contains only the absolute-value preliminaries listed above.
- The last theorem does not need K and L to be number fields. It does need the separability of L/K and the nontriviality of vK.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/AbsoluteValue.lean`: the Lean file is the source byte for byte (SHA-256 `cb83b5ff92455d4ce1912e18d2ae9f5ad9eabcde78af3a74ec3251ecaa4fd0ba`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
