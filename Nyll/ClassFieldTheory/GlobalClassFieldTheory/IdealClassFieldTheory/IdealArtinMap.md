# The ideal-theoretic Artin map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field, N a subgroup of the idele class group C_K, and m a modulus whose congruence subgroup C_K^m lies in N (hypothesis `hm`). Then C_K → C_K/N factors through the ray class group mod m, which gives an Artin map on fractional ideals prime to m. The file proves it is surjective and computes its kernel when N is the norm group of a finite extension. For abelian L/K it also gives the map with values in Gal(L/K).

## Main definitions and results

- `rayClassToNormQuotient`, `idealRayClassArtinMap`, `idealArtinMap`: these maps send the idelic ray class group, the ideal ray class group I^m/P^m, and the group I^m of ideals prime to m onto C_K/N. All three are surjective (`idealArtinMap_surjective` and companions).
- `idealArtinMap_primeToIdealMap`: for an idele a prime to m, the Artin map sends the ideal of a to the class of a.
- `idealArtinKernel`: the ideal group H_m, defined as the kernel. It contains the principal ray ideals. `idealArtin_exact` records 1 → H_m → I^m → C_K/N → 1.
- `normIdeleLiftedModulus m`: for finite L/K, a modulus of L. It keeps the finite part of the lifted modulus `idealNormLiftedModulus m` and adds all real places of L. The idele norm sends ideles prime to it to ideles prime to m (`ideleNorm_mem_idelePrimeToModulusSubgroup`). The restricted norm `primeToModulusIdeleNorm` is compatible with the ideal norm.
- `idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension`: for finite L/K and N = N(C_L), H_m equals `RayClass.idealNormSubgroup m`, that is the norms of ideals of L prime to the lifted modulus, times the principal ray ideals P^m. `idealArtinKernel_eq_idealNormSubgroup` restates this.
- `idealArtinGaloisMap`: for abelian L/K, `idealArtinMap` followed by the global norm-residue isomorphism `Reciprocity.globalNormResidueEquiv` : C_K/N(C_L) ≃ Gal(L/K). It is surjective, its kernel is H_m, and `idealArtinGalois_exact` gives the exact sequence 1 → H_m → I^m → Gal(L/K) → 1.

## Proof

The factorization uses the imported isomorphism between the idelic and ideal ray class groups. For the kernel, lift an ideal in H_m to an idele a prime to m. The class of a is a norm, and a principal adjustment makes the preimage prime to the lifted modulus. So the ideal is a norm times a principal ray ideal. The reverse inclusion uses compatibility of idele and ideal norms, and positivity of local norms at real places.

## Points to watch

- N is any subgroup containing C_K^m. Only the kernel theorem and the Galois-valued map concern norm groups.
- `idealArtin_exact` holds largely by definition: H_m is defined as the kernel.
- The kernel theorem needs only a finite extension. Despite its section, `idealArtinKernel_eq_idealNormSubgroup` omits the Galois hypothesis.
- This file does not say which Frobenius normalization `idealArtinGaloisMap` has.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/IdealArtinMap.lean`: the Lean file is the source byte for byte (SHA-256 `4275b5cc69e650bc92c0659f13c6268fd28356e8c8ec22911bb4456980cd5ac9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
