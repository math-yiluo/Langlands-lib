# Coefficient equations for a fixed uniformizer

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Elementary facts about a uniformizer π of a local field K, used to solve the coefficient equations of the Lubin–Tate construction degree by degree: for r ≥ 1, 1 − π^r is a unit of the valuation ring, so (1 − π^r)·x = b has exactly one solution.

## Main results

All in the namespace `LubinTate.SameUniformizer`.

- `residueMap_uniformizer_eq_zero`, `residueMap_uniformizer_pow_eq_zero`: π, and π^r for r ≠ 0, reduce to zero in the residue field.
- `uniformizer_dvd_of_residueMap_eq_zero`: an element of the valuation ring reducing to zero is divisible by π.
- `isUnit_one_sub_uniformizer_pow`: for r ≠ 0, 1 − π^r is a unit.
- `existsUnique_mul_eq_of_isUnit`: in a commutative ring, a·x = b has a unique solution when a is a unit.
- `existsUnique_one_sub_uniformizer_pow_mul_eq`: for r ≠ 0 and any b in the valuation ring, (1 − π^r)·x = b has a unique solution x.

## Proofs

1 − π^r is a unit in the local valuation ring because π^r is a nonunit, its residue being zero.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/CoefficientEquation.lean`: the Lean file is the source byte for byte (SHA-256 `08432f743c414b0de5c954524997a6bafd167b3098e7971bd49dd944d2f8f50b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
