# Arithmetic Frobenius at an unramified finite place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be an abelian extension of number fields and `v` a finite place of `K`. The local class-formation coordinate used elsewhere in the library has geometric Frobenius normalization. This file defines the arithmetic Artin element of `v` and identifies it with arithmetic Frobenius when the chosen completion at `v` is unramified.

## Main definitions and results

- `arithmeticFinitePlacePrimeArtin v`: the image of the normalized prime idele at `v` under the arithmetic global Artin map. It equals the chosen local arithmetic Artin value of the chosen element of normalized local order one, `FiniteIdeleGroup.chosenLocalOrderSection v 1` (`..._eq_arithmeticChosenFinitePlaceArtin`), the global norm-residue symbol of the prime idele class (`..._eq_arithmeticGlobalNormResidue`), and the inverse of the geometric `finitePlacePrimeArtin v` (`..._eq_inv`).
- `chosenFinitePlaceArithmeticFrobenius v hunram`: the arithmetic Frobenius of the chosen completed extension at `v`, carried into `Gal(L/K)` through the decomposition group; it requires `hunram : ChosenFinitePlaceIsUnramified v`.
- `arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius`: at such `v` the two agree.
- `orderOf_arithmeticFinitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified`: its order is the local degree at `v`.
- `arithmeticFinitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified`: it is trivial iff `v` splits completely.

The last two follow from the geometric versions, since an element and its inverse have the same order.

Unramifiedness is that of the chosen completed extension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ArithmeticUnramifiedPrimeArtin.lean`: the Lean file is the source byte for byte (SHA-256 `5213b137ca69b45b7671f38d95737005066ee70ef0dadfe8f6483cde76f7d2c7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
