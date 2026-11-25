# The decomposition law for unramified primes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealDecompositionLaw`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields and m a defining modulus for it: the congruence subgroup of m lies in N(C_L). Write H_m for the kernel of the ideal Artin map on ideals prime to m. The file identifies the ideal Artin symbol of a prime with its prime Artin element. For unramified primes it derives the decomposition law. It ends with splitting in the small Hilbert class field.

## Main results

- `idealArtinGaloisMap_primeToIdealMap_eq_globalArtin`: for an idele prime to m, the ideal Artin symbol of its ideal is its global Artin automorphism.
- `idealArtinGaloisMap_primeIdeal_eq_finitePlacePrimeArtin`, `..._eq_chosenFinitePlaceArtin` and `idealClassQuotientEquivGaloisGroup_primeIdeal`: a prime v ∤ m goes to `finitePlacePrimeArtin v`, that is, to the chosen local Artin value of a uniformizer, a local element of normalized valuation 1.

The following assume that the chosen completion of L above v is unramified (`ChosenFinitePlaceIsUnramified v`):

- `ramificationIndex_eq_one_of_chosenFinitePlaceUnramified`: the ramification index of v in 𝓞 L is 1.
- `finitePlaceLocalDegree_eq_inertiaDegree_of_chosenUnramified`: the local degree equals the inertia degree f.
- `orderOf_idealPrimeClass_eq_inertiaDegree_of_chosenUnramified` (v ∤ m): the order of the class of v in I^m/H_m is f. `unramifiedPrime_pow_mem_idealArtinKernel_iff_inertiaDegree_dvd`: vⁿ ∈ H_m if and only if f ∣ n.
- `unramifiedPrime_idealMap_eq_product_primesOver`: v 𝓞 L is the product of the distinct primes above v. `unramifiedPrime_numberOfPrimes_eq_extensionDegree_div_inertiaDegree`: their number is [L : K] / f.
- `unramifiedPrime_idealDecompositionLaw`: the three statements together, with f the order of v in I^m/H_m.
- `primeAbove_inertiaDegree_eq_common`, without the unramified hypothesis: all primes above v have the same inertia degree.

For the selected small Hilbert class field H of K:

- `smallHilbertClassFieldGaloisEquivClassGroup_finitePlacePrimeArtin`: the imported isomorphism Gal(H/K) ≃ Cl(K) sends the prime Artin element of v to the ideal class of v.
- `smallHilbertClassField_chosenFinitePlaceIsUnramified`: every finite place is unramified in H.
- `finitePlaceSplitsCompletelyInSmallHilbertClassField_iff_principal`: v splits completely in H if and only if the prime ideal v is principal.

## Proof

The order of the prime Artin element is the local degree (imported). The local degree is the order of the decomposition group, the stabilizer of a prime above v, which is e·f with e = 1. The prime count and factorization come from the Galois prime-decomposition results for Dedekind domains in `HilbertRamification.Dedekind`.

## Points to watch

- Unramifiedness is assumed for the library's chosen completion above v, separately from v ∤ m.
- The docstrings call `finitePlacePrimeArtin` the Frobenius automorphism. This file reaches it by evaluating reciprocity on the prime idele, and then uses only its order, the local degree. It does not show its action on residue fields.
- [L : K] / f is division in ℕ.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/IdealDecompositionLaw.lean`: the Lean file is the source byte for byte (SHA-256 `dcdafc3eb6dbcafd10e454d9c3c5f99591f17400ef78831c1dd733a3d6793fd0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
