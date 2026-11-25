# The normalized valuation of a local field as a Henselian valuation

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalHenselianValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K`, this file builds `localHenselianValuation K`, a term of the class formation's `ValuationData` for the residue Frobenius degree datum `localResidueDatum K` and the units of `SeparableClosure K`. Its underlying map is the normalized valuation of `K` with values in `ZHat` (`localBaseValuation`).

The fields of the structure are filled as follows: the integers lie in the value group, and the quotient of the value group by `n`-multiples maps bijectively to `ZMod n`, both from earlier results; for every finite abstract field `H`, possibly non-normal, the image of the norm to the base composed with the valuation is the residue-degree multiple of the value group. For the last one, the fixed field `E` of `H` is given the spectral norm extending the absolute value of `K`. The file checks that `E` is then a nonarchimedean local field whose valuation extends that of `K`, with valuation ring integral over that of `K` (via the minimal polynomial and the spectral value bound), and applies the residue-degree comparison `localBaseValuation_comp_normToBase_range_eq_residueFinrank`.

`localHenselianValuation` is a definition, and `ValuationData` is the library's own notion from its abstract class field theory. The field `K` is taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalHenselianValuation.lean`: the Lean file is the source byte for byte (SHA-256 `136ac833f9ad7ca516c071fe1a00dde75f9e1bc15cc5fecce8ffa866e13980d8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
