# Norms of fractional ideals prime to a modulus

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of number fields, this file defines the relative norm of fractional ideals (a prime `W` above `v` goes to `v^f`, `f` the inertia degree), relates it to the idele norm, and restricts it to ideals prime to a modulus. Given a modulus `m` of `K`, it chooses a modulus of `L` deep enough at the primes above `m` that local norms respect the higher-unit conditions of `m`. It then defines the norm-defined ideal group of `m`.

## Main definitions and results

- `RayClass.exists_localHigherUnitGroup_le_norm_preimage`: for a prime `W` of `𝓞 L` over `v`, some `U_W^(n)` has local norm inside `U_v^(m(v))`.
- `RayClass.idealNormLiftedModulusExponent m W`: one more than the least such `n` when `v` is in the support of `m`, and `0` otherwise, with lemmas on its properties.
- `RayClass.idealNormLiftedModulus m`: the modulus of `L` with these exponents and no real places; its support is the finite set of primes above the support of `m`.
- `RayClass.idealNormExponentMap`: the push-forward of exponent vectors, `W` contributing `f(W|v)` times its exponent to `v`.
- `RayClass.fractionalIdealNorm`: the norm `FractionalIdealGroup L →* FractionalIdealGroup K` obtained through prime factorization; `count_fractionalIdealNorm` gives its exponents, and `fractionalIdealNorm_eq_public` shows it equals the library's public `ClassFieldTheory.fractionalIdealNorm K L`.
- `IdeleGroup.count_fractionalIdeal`: the exponent at `v` of the ideal of an idele is the order of its `v`-component. `IdeleGroup.fractionalIdeal_ideleNorm`: the ideal of the idele norm of `a` is the norm of the ideal of `a`.
- `RayClass.primeToModulusIdealNorm m`: the norm from ideals prime to the lifted modulus to ideals prime to `m`.
- `RayClass.finite_norm_mem_finitePrimeToModulusSubgroup`: for an idele prime to the lifted modulus, the finite part of its norm satisfies the finite higher-unit conditions of `m`.
- `RayClass.idealNormSubgroup m`: the image of `primeToModulusIdealNorm m` joined with the principal ray ideals `P_K^m`, inside the ideals prime to `m`.

## Proof

The depth exists because the local norm is continuous on units and the higher unit groups form a basis of neighbourhoods of `1`. Compatibility with the idele norm compares, prime by prime, the order of a local norm with `f` times the order upstairs (an imported local fact).

## Points to watch

- The lifted modulus is a choice made in this file: least depth plus one, with no archimedean part. It is not `m 𝓞_L`, nor a conductor-type modulus. For fractional ideals, being prime to it depends only on its support; for ideles the exponents matter.
- Only the finite part of the norm is controlled; positivity at real places is not addressed here.
- The norm is the library's construction via exponents and inertia degrees; it is compared with the library's public definition, not with a Mathlib norm of ideals.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/IdealNorm.lean`: the Lean file is the source byte for byte (SHA-256 `515fc937fc5ad357f0f19386b0217c0ae6b70f197faa68db41369e7070017dfd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
