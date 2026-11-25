# Ideals prime to a modulus and the ideal-theoretic ray class group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` and a modulus `m` (a finite part and a set of selected real places), this file defines the group `J^m` of fractional ideals prime to `m` and the ideal-theoretic ray class group `J^m / P^m`. It proves that this group is isomorphic to the idelic ray class group, using weak approximation at the places of `m`.

## Main definitions and results

- `RayClass.primeToModulusIdeals m`: fractional ideals with exponent `0` at every prime in the support of the finite part of `m`; `primeToModulusIdeal` views a prime outside the support as an element.
- `RayClass.idelePrimeToModulusSubgroup m`, written `I_K^(m)`: ideles in the infinite congruence subgroup of `m` whose components at primes `v` of the support lie in `U_v^(m(v))`; no condition at other finite places.
- `RayClass.primeToIdealMap m`: the fractional-ideal map `I_K^(m) → J^m`. It is surjective (`primeToIdealMap_surjective`), its kernel is the idele congruence subgroup of `m` (`primeToIdealMap_ker`), and `quotientCongruenceEquivPrimeToIdeals` is the resulting isomorphism.
- `RayClass.principalRayIdealSubgroup m`, written `P^m`: the ideals `(x)` for `x ∈ Kˣ` whose principal idele lies in `I_K^(m)` (`mem_principalRayIdealSubgroup_iff`). `RayClass.IdealRayClassGroup m` is `J^m / P^m`; `quotientRaySubgroupEquivIdealRayClassGroup` identifies it with `I_K^(m)` modulo the congruence and principal ideles in it.
- Approximation: `ApproximationPlace m` (support of `m` and all archimedean places), the nontrivial, pairwise inequivalent absolute values at these places, and `denseRange_approximationEmbedding`: `K` is dense in the product of the completions.
- `unitRatioSet a U`: elements `y` with `a y⁻¹ ∈ U`, open when `U` is.
- `exists_principal_quotient_mem_primeTo`: for every idele `a` some `x ∈ Kˣ` has `a x⁻¹ ∈ I_K^(m)`; hence `idelePrimeToModulusSubgroup_sup_principalSubgroup`: `I_K = I_K^(m) Kˣ`.
- `quotientRaySubgroupEquivIdeleRayQuotient`: the same quotient of `I_K^(m)` is isomorphic to `I_K / (ideleCongruenceSubgroup m ⊔ Kˣ)`.
- `RayClass.rayClassGroupEquivIdealRayClassGroup`: `RayClassGroup m ≃* IdealRayClassGroup m`.

## Proof

Surjectivity onto `J^m` uses an idele with prescribed valuations, `1` on the support. Density comes from an imported weak approximation theorem for finitely many pairwise inequivalent absolute values; inequivalence is checked here, by an element in one prime and not another, and by `|2| ≤ 1` at finite places. The approximating `x` is nonzero because it lies in a unit coset at an archimedean place. The final isomorphism composes the isomorphism theorems above.

## Points to watch

- The docstring of `principalRayIdealSubgroup` says "totally positive", but the definition imposes positivity only at the real places selected by `m`; the two agree for the narrow modulus.
- The isomorphism of ray class groups is built abstractly; the file gives its value only through the projections from `I_K^(m)`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Ideal.lean`: the Lean file is the source byte for byte (SHA-256 `63643f0ba50915aea295db1207c15d759916963ee69c812741257921155eaadd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
