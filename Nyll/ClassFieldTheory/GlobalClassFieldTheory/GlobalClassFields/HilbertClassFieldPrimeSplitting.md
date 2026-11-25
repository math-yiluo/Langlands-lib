# Prime splitting in cyclic extensions of Hilbert class field degree

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldPrimeSplitting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a cyclic extension of number fields unramified at every finite prime. There are two cases. If [L : K] equals the order of the narrow class group Cl⁺(K), then C_K/N is identified with Cl⁺(K), where N is the idèle-class norm group of L/K. If moreover L/K is unramified at the infinite places and [L : K] equals the class number h_K, then it is identified with the class group Cl(K). This file transports the Frobenius class of a prime v across these identifications. It shows that the class is trivial exactly when v has a totally positive generator, respectively a generator. It also shows that primes which split completely in L have that property.

## Main definitions and results

- `bigHilbertFrobeniusClass v` and `bigHilbertFrobeniusClass_eq_one_iff_exists_totallyPositiveGenerator`: the class of v in the big Hilbert quotient is trivial exactly when v = (x) for some x ∈ Kˣ positive at every real place.
- `maximalFiniteUnramifiedCyclicFrobeniusClass` (hypotheses `hunramified` and `hdegree : [L : K] = |Cl⁺(K)|`): the Frobenius class in C_K/N. It is represented by the one-place prime idèle at v, has the order of the narrow class of v, and is trivial exactly when v has a totally positive generator.
- `finitePlaceSplitsCompletely_imp_exists_totallyPositiveGenerator_of_maximalFiniteUnramifiedCyclic`: a prime that splits completely in such an L has a totally positive generator.
- `maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient` and `maximalEverywhereUnramifiedCyclicFrobeniusClass` (with `hdegree : [L : K] = h_K` and `IsUnramifiedAtInfinitePlaces K L`): the identification with the small Hilbert quotient and the Frobenius class. That class is represented by the prime idèle and has the order of the ideal class of v.
- `maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one_iff_smallHilbertClassFieldSplitsCompletely`, `..._eq_one_iff_principal` and `..._eq_one_iff_exists_generator`: the class is trivial if and only if v satisfies the library's predicate `SplitsCompletelyInSmallHilbertClassField`, if and only if v is principal.
- `finitePlaceSplitsCompletely_imp_prime_principal_of_maximalEverywhereUnramifiedCyclic` and its contrapositive `not_finitePlaceSplitsCompletely_of_prime_not_principal_of_maximalEverywhereUnramifiedCyclic`: a prime splitting completely in L is principal, and a non-principal prime does not split completely.

## Proof

The identifications come from the degree criteria of the Hilbert class field maximality file. The totally positive generator criterion unwinds membership of the prime idèle in the narrow congruence subgroup times Kˣ. Complete splitting gives triviality because the one-place idèles at a completely split prime are norms.

## Points to watch

- Only one direction is proved for actual splitting in L: complete splitting implies a (totally positive) generator. The converse is not stated.
- `SplitsCompletelyInSmallHilbertClassField` is the library's own predicate from its ideal-theoretic class field theory, not splitting in the field L.
- Both settings are restricted to cyclic extensions whose degree equals the relevant class number, passed as hypotheses.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldPrimeSplitting.lean`: the Lean file is the source byte for byte (SHA-256 `2ae00a2875e55b58e9887bb3c03eed7d1b92560af2013d3a4607e719c34ce5b3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
