# The ideal class-field isomorphism

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field, N a subgroup of the idele class group C_K, and m a modulus whose congruence subgroup lies in N. The ideal Artin map from the group I^m of fractional ideals prime to m onto C_K/N is surjective. Its kernel is H_m, by definition of H_m. This file applies the first isomorphism theorem to obtain I^m/H_m ≃ C_K/N. For a finite abelian extension L/K it gives the analogue with Gal(L/K).

## Main definitions and results

- `idealClassQuotientEquivNormQuotient m N hm`: the isomorphism I^m/H_m ≃* C_K/N. It sends the class of an ideal to its image under `idealArtinMap` (`idealClassQuotientEquivNormQuotient_mk`).
- `idealClassQuotient_mk_eq_one_iff`: an ideal has trivial class in I^m/H_m if and only if its Artin image is trivial.
- `idealClassQuotientEquivGaloisGroup m hm`: for abelian L/K and N = N(C_L), the isomorphism I^m/H_m ≃* Gal(L/K). It is the previous isomorphism followed by the global norm-residue isomorphism `Reciprocity.globalNormResidueEquiv`. On representatives it is `idealArtinGaloisMap`.
- `idealClassQuotient_mk_eq_one_iff_galoisArtin_eq_one`: an ideal has trivial class if and only if its Galois-valued Artin symbol is trivial.

The file also makes the normality of H_m a local instance, `idealArtinKernelNormal`.

## Points to watch

The hypothesis is only that m is a defining modulus (C_K^m ≤ N); m need not be the conductor.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/IdealArtinQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `1a1cf9416bb7c8f9ccbe24d2292d0bc1cfe1f90561401946614bbf6e2dd9a8be`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
