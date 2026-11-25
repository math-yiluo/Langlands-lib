# Local solutions and integral closures over discrete valuation rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.LocalSolutions`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file describes the local rings of integral closures in reduced Artinian algebras and combines the solutions at finitely many maximal ideals into one finite extension of the original fraction field.

## Results

- `isDiscreteValuationRing_integralClosure_localization` gives a domain and a DVR at each maximal ideal of the integral closure of a DVR R in a reduced Artinian algebra T over a field containing R, provided the integral closure is Noetherian. If a prime localization is a DVR and the map from R is injective and local, `exists_isLocalization_fractionRing_atPrime_integralClosure` identifies its fraction field as the localization of T at the image of the prime complement. The latter assumes T integral over the fraction ring of R.
- `isDedekindDomain_integralClosure_of_integral_base` shows that the integral closure of A in a finite extension of the fraction field of R is Dedekind when R is integral over A, Noetherian, a domain, and of dimension at most one.
- `exists_finite_extension_localSolutions_of_perfectField` starts with a DVR A with perfect residue field and an A-algebra C with finitely many maximal ideals. Each maximal localization of C must be a DVR extension of A whose residue field is essentially of finite type over that of A. The theorem equips their fraction fields with compatible algebras over the fraction field K of A and finds a single finite K-extension giving an `IntegralClosureBaseChange.IsSolution` at each localization.

For the DVR result, the reduced Artinian ring splits into field factors. Integral closure is computed componentwise and localization selects one Dedekind factor. To combine solutions, the proof embeds the individual finite extensions in an algebraic closure, takes their compositum, and uses persistence of solutions up finite extension towers. Other lemmas track contraction of maximal ideals, injectivity along integral towers, and finite generation of residue fields under localization.

The common-extension theorem assumes `hEpp`, an instance of Epp’s theorem for the relevant universes. The common extension lives in the universe of K, and the formal-smoothness tests in its solutions use the maximum of the universes of K and C.

## References

Stacks Project Tag 09II, Tag 09F9 and Tag 0GLR. The implication from maximal-ideal contraction to locality in `isLocalHom_localization_of_comap_eq_maximalIdeal` is cited as EGA I 8.1.1, (i) ⇒ (ii).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 8.1.1 | `isLocalHom_localization_of_comap_eq_maximalIdeal` | (i) ⇒ (ii) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EliminateRamificationSolution/LocalSolutions.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 20 are kept. The 4 left out are not needed by the results for which the extract is made: `Stacks.EliminateRamification.exists_subalgebra_eq_top_of_directed_cover`, `Stacks.EliminateRamification.integralClosure_finiteProduct_dedekind`, `Stacks.EliminateRamification.integralClosure_isDedekind_of_fractionRing_range`, `Stacks.EliminateRamification.isScalarTower_of_isLocalization_base`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
