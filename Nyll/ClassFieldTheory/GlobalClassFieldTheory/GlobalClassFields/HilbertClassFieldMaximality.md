# Degree criteria for cyclic Hilbert class fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldMaximality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite cyclic extension of number fields. If L/K is unramified at every finite prime, its idèle-class norm group contains the big Hilbert norm subgroup, whose quotient is the narrow class group Cl⁺(K). If L/K is also unramified at the infinite places, its norm group contains the small Hilbert norm subgroup, whose quotient is the class group Cl(K). This file shows that equality holds exactly when the degree [L : K] attains |Cl⁺(K)|, respectively the class number h_K. It then derives uniqueness and maximality statements.

## Main results

- `ideleClassNorm_range_eq_bigHilbertClassFieldNormSubgroup_iff_finrank_eq_narrowClassGroup_card`: suppose no finite place of K ramifies in L (hypothesis `ramifiedBaseFinitePlaces = ∅`). Then the idèle-class norm group N of L/K is the big Hilbert subgroup if and only if [L : K] = |Cl⁺(K)|.
- `narrowClassGroupToIdeleClassNormQuotient_injective_iff_finrank_eq_narrowClassGroup_card` and `maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup`: under the same condition, the surjection Cl⁺(K) → C_K/N is injective exactly at that degree, and then C_K/N ≅ Cl⁺(K).
- `ideleClassNorm_range_eq_smallHilbertClassFieldNormSubgroup_iff_finrank_eq_classNumber`, `classGroupToIdeleClassNormQuotient_injective_iff_finrank_eq_classNumber` and `maximalEverywhereUnramifiedCyclicNormQuotientEquivClassGroup`: the same three statements for the small Hilbert subgroup and Cl(K). They assume in addition `IsUnramifiedAtInfinitePlaces K L`.
- `maximalFiniteUnramifiedCyclicNormRanges_eq` and `maximalEverywhereUnramifiedCyclicNormRanges_eq`: two such cyclic extensions of maximal degree have the same norm group.
- `maximalFiniteUnramifiedCyclicExtension_relativeDegree_eq_one` and `maximalEverywhereUnramifiedCyclicExtension_relativeDegree_eq_one`: suppose [L : K] equals |Cl⁺(K)| (respectively h_K), and M ⊇ L is cyclic over K and unramified in the corresponding sense. Then M = L in degree. The two `properCyclicOverextension_..._has_ramifiedFinitePlace` results are the contrapositive: a cyclic M/K with [M : L] ≠ 1 ramifies at some finite place. In the class-number case this still assumes `IsUnramifiedAtInfinitePlaces K M`.

## Proof

The norm index theorem for cyclic extensions, `ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic`, gives |C_K/N| = [L : K]. The imported inclusion of the Hilbert subgroup in N then becomes an equality when the indices agree. The relative-degree statements use the imported divisibility of the degree of an unramified cyclic extension into |Cl⁺(K)| or h_K.

## Points to watch

- The norm-group results are stated for cyclic extensions only. In the relative-degree results and their contrapositives, M/K must be cyclic, but L/K need only be finite Galois with the stated degree: cyclicity of L/K is not assumed there, and neither is unramifiedness of L/K. The uniqueness results concern norm subgroups, not fields. Maximality is shown only against cyclic overextensions M of K that contain L.
- "Unramified" means unramified at finite primes for the big (narrow) Hilbert field. It means unramified at finite primes together with `IsUnramifiedAtInfinitePlaces` for the small one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldMaximality.lean`: the Lean file is the source byte for byte (SHA-256 `04180e0de815c75b9acf6365c1045b4c0f6b2888f8c4f50659a07800e45ec97e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
