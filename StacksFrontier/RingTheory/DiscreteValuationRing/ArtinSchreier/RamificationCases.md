# Ramification of Artin–Schreier extensions of a discrete valuation field

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.RamificationCases`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a discrete valuation ring whose fraction field K has characteristic p > 0, and let L = K[z] with z^p − z = ξ in K. This file proves that L/K is Galois and falls into one of four ramification alternatives, and gives conditions on ξ, relative to a uniformizer π, that narrow down which alternative holds.

## Main result

`isGalois_and_ramification_cases_of_adjoin_root_artinSchreier` (Tag 09F0): with L = K[z] written `Algebra.adjoin K {z} = ⊤` and B the integral closure of A in L, L/K is finite and Galois, and one of the following holds:

- trivial: K → L is surjective;
- unramified: [L : K] = p and every maximal ideal of B has ramification index one with separable residue extension;
- totally ramified: in the sense of `Stacks.KummerExtension.IsTotallyRamified`, with ramification index p at every maximal ideal;
- residually inseparable: B is a discrete valuation ring with ramification index one and purely inseparable residue extension of degree p.

Moreover: if ξ lies in A, the extension is trivial or unramified; if ξ = π^(−n) a with a a unit and n > 0 prime to p, it is totally ramified; if ξ = π^(−n) a with n > 0 divisible by p and the residue of a not a p-th power, it is residually inseparable.

## Supporting results

- `unramified_of_separable_minpoly`: over a Dedekind domain R with fraction field K and L/K finite separable, if L = K[x] with x integral over R and its minimal polynomial separable modulo the prime under a nonzero prime P, the integral closure is unramified over R at P.
- `valuation_aeval_le_one`, `valuation_aeval_eq_pow_of_one_lt`, `natDegree_dvd_of_valuation_aeval_eq_exp`: valuations of values of monic polynomials with integral coefficients; a value of valuation exp N forces the degree to divide N.
- `natDegree_dvd_ramificationIdx_of_coprime_pole`: if P is monic over A of degree p, L/K finite separable, and P(z) = π^(−n) a with a a unit and n > 0 coprime to p, then p divides every ramification index over m_A.
- `totally_ramified_of_coprime_pole`: if moreover L/K is Galois and [L : K] divides the prime p, L/K is totally ramified with index p.

## Proof

The alternative comes from `ramification_cases_of_isGalois_of_finrank_dvd_prime` and companions in the imported Galois-degree file; each criterion excludes the incompatible cases.

## Points to watch

- The alternatives are the file's own formulations through the integral closure and `Ideal.ramificationIdx'`; total ramification is the library's notion, not Mathlib's.
- The second and third criteria take ξ exactly of the form π^(−n) a, for the fixed uniformizer π.

## References

Tag 09F0.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09F0](https://stacks.math.columbia.edu/tag/09F0) | `isGalois_and_ramification_cases_of_adjoin_root_artinSchreier` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier/RamificationCases.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
