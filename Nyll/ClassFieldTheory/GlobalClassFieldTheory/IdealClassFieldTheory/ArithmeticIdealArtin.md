# The ideal Artin map in arithmetic normalization

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields and m a modulus of K that defines L. This means the congruence subgroup of m lies in the norm range N(C_L) (hypothesis `hm`). The file builds the Artin map on ideals prime to m with values in Gal(L/K), normalized so that primes go to the arithmetic prime Artin element. It identifies its kernel and the induced isomorphism.

## Main definitions and results

- `arithmeticIdealArtinGaloisMap m hm`: from the group of fractional ideals prime to m to Gal(L/K). It is the ideal-to-idele-class map `idealArtinMap` followed by the arithmetic global norm-residue isomorphism C_K/N(C_L) ≃ Gal(L/K).
- `arithmeticIdealArtinGaloisMap_eq_inv_idealArtinGaloisMap`: it is the pointwise inverse of the library's other normalization, `idealArtinGaloisMap`.
- `arithmeticIdealArtinGaloisMap_surjective`, and `arithmeticIdealArtinGaloisMap_ker`: the kernel is `idealArtinKernel`, the same ideal group as for the other normalization.
- `arithmeticIdealClassQuotientEquivGaloisGroup`: the induced isomorphism from ideals prime to m modulo that kernel onto Gal(L/K).
- `arithmeticIdealArtinGaloisMap_primeToIdealMap_eq_globalArtin`: on ideles prime to m, the ideal Artin map applied to the associated ideal equals the arithmetic idelic Artin map.
- `arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin`, its local form `..._eq_arithmeticChosenFinitePlaceArtin`, and `arithmeticIdealClassQuotientEquivGaloisGroup_primeIdeal`: a prime v not dividing m goes to `GlobalClassFields.arithmeticFinitePlacePrimeArtin v`. Equivalently, it goes to the arithmetic chosen local Artin value of an element of normalized order 1.

## Proof

The statements reduce to imported facts. The ideal of the one-place prime idele at v is the prime ideal v. The global norm-residue map on such ideles is the chosen local Artin map.

## Points to watch

- The header speaks of arithmetic Frobenius. The theorems themselves give `arithmeticFinitePlacePrimeArtin v`, which is defined in an imported file through reciprocity. This file does not compare it with the action on residue fields.
- The modulus is given with a proof `hm` that it is a defining modulus. It need not be the conductor.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/ArithmeticIdealArtin.lean`: the Lean file is the source byte for byte (SHA-256 `9865767bce598c8e65062d8b680a5972a33cc4462d59175d578cf928b75bf284`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
