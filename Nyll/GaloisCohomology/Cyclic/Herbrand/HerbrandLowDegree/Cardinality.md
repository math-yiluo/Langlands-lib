# Six-term cardinality identity for low-degree Tate groups

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `G` be a finite group with generator `σ` and `1 → A → B → C → 1` a short exact sequence of multiplicative `G`-modules. For each module the file forms the 2-periodic chain complex of `ℤ`-modules whose differentials alternate between the norm and `σ − 1`, takes Mathlib's long exact homology sequence of the resulting short exact sequence of complexes, and reads off finiteness and cardinality statements for the library's groups `HerbrandH0` and `HerbrandHMinusOne`.

## Main definitions and results

- `HerbrandQuotientDefined G A σ`: the proposition that `HerbrandH0 G A` and `HerbrandHMinusOne G A σ` are both finite.
- `herbrandQuotientDefined_anyTwo_of_periodic`: given equivariant `i : A →* B` and `j : B →* C` with `ker j = im i` (`hker`), `i` injective, `j` surjective, and `σ` generating `G`, if two of `A`, `B`, `C` satisfy `HerbrandQuotientDefined`, so does the third.
- `herbrand_exact_cardinality_identity`: under the same hypotheses, with all six groups finite,
  `#Ĥ⁰(B) · #Ĥ⁻¹(A) · #Ĥ⁻¹(C) = #Ĥ⁰(A) · #Ĥ⁰(C) · #Ĥ⁻¹(B)`.
- Public helpers on `ModuleCat ℤ`: exactness passes to the underlying groups written multiplicatively (`mulExact_of_moduleCat_exact`, `mulExact_of_moduleCat_shortComplex_exact`); at an exact spot with finite middle term, its order is the product of the orders of the two ranges (`moduleCat_card_eq_card_range_mul_card_range_of_exact`); conjugate morphisms have ranges of equal order (`moduleCatRangeCard_eq_of_conjugate`); finiteness passes along isomorphisms and to the middle of an exact pair (`finite_source_of_moduleIso`, `finite_target_of_moduleIso`, `finite_middle_of_exact`, `finite_middle_of_moduleCat_exact`); `moduleCat_card_eq_of_iso`.

## Proofs

In the periodic complex, homology in even positive degrees is identified with `Ĥ⁻¹` and in odd degrees with `Ĥ⁰`, through `subNormHomologyEquivHerbrandHMinusOne` and `normHomologyEquivHerbrandH0` (the latter uses the generator). The six terms of the long exact sequence in degrees 4, 3 and 2 are finite; each order is the product of two range orders; the maps induced by `i` in degrees 4 and 2 have ranges of the same order by periodicity; multiplying out gives the identity. For the third module, homology in degrees 3 and 4 is finite as the middle term of an exact pair with finite outer terms.

## Points to watch

- `A`, `B`, `C` lie in one common universe; `G` may lie in another.
- Both theorems need `σ` to generate `G`.
- `HerbrandQuotientDefined` is the library's own notion.
- The identity is an equation of natural numbers and does not mention `herbrandQuotient`. It assumes all six groups finite; only the first theorem derives finiteness for one module from the other two.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`: the Lean file is the source byte for byte (SHA-256 `ddffd990bf42592b91ecb6e30cbc5ab60613b77da4b744a366f6dc2ec180ae81`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
