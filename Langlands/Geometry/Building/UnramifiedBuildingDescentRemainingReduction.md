# Unramified building descent from its seven remaining inputs

This module refines the published reduction
`Langlands.Geometry.Building.unramifiedBuildingDescentReduction`. That reduction derives the
target `UnramifiedBuildingDescentStatement` from nine inputs. Two of them are now proved:

- `QuasiSplitIntegerApartmentExistenceStatement`, by the published
  `quasiSplitIntegerApartmentExistence` (`QuasiSplitIntegerApartmentExistenceProof`);
- `MaximalUnramifiedApartmentInjectiveStatement`, by `maximalUnramifiedApartmentInjective`
  in the companion module `MaximalUnramifiedApartmentInjective`, submitted with this one.

The module states the reduction from the seven inputs that remain and proves it. It adds no
mathematical content of its own. Its provenance is internal: it is a bookkeeping step
in the formal proof of the target, and it records which inputs are still open. The source
results of the remaining inputs are those cited in their own modules and in
`UnramifiedBuildingDescentReduction.md` (Kaletha–Prasad 2023, Chapters 7 and 9).

## `UnramifiedBuildingDescentRemainingReductionStatement`

The proposition is the implication, at universe `u`, with hypotheses in this order:

1. `UnramifiedQuasiSplitStatement`: every connected reductive group over the maximal
   unramified extension `K` of a nonarchimedean local field has a field-defined geometric
   Borel subgroup;
2. `SpecialTorusExistenceStatement`: every maximal `F`-split torus `S` lies in a closed
   `F`-subgroup `T` with `T_K` a maximal `K`-split torus of `G_K` (KP Proposition 9.3.4);
3. `UnramifiedValuationDescentStatement`: restricting the `Aut(K/F)`-fixed points of a class
   over `K` satisfying V 6 from `T_K` to `S` and from `K` to `F` gives an `N(F)`-stable class
   over `F` satisfying V 6 (KP Construction 9.6.1, Lemma 9.6.3 and Theorem 9.6.5);
4. `ValuationBuildingApartmentAxiomsStatement`: every `ValuationBuildingData` over a
   nonarchimedean local field satisfies V 7 and AS 2–AS 5 (KP §9.5, Theorem 9.6.5, §9.6.6);
5. `ChapterSevenBuildingAxiomsStatement`: under the apartment axioms, the existing quotient
   satisfies the building axioms of the opening of KP Section 4.2 (KP Chapter 7);
6. `UnramifiedGaloisFixedBuildingPointStatement`: Galois-fixed points of the building
   over `K` come from fixed apartment points (KP Theorem 9.2.7 and §9.3);
7. `UnramifiedSpecialPointDescentStatement`: special points descend (KP
   Proposition 9.9.2).

The conclusion is `UnramifiedBuildingDescentStatement`. All seven hypotheses and the
conclusion are the existing Library statements, used at the same universe `u`. The inputs
are the hypotheses 1, 3, 4, 5, 6, 8 and 9 of `UnramifiedBuildingDescentReductionStatement`,
in their original order.

## `unramifiedBuildingDescentRemainingReduction`

Given the seven hypotheses, apply `unramifiedBuildingDescentReduction`. Its second input is
`quasiSplitIntegerApartmentExistence` and its seventh is
`maximalUnramifiedApartmentInjective`; the other seven are the hypotheses, in order.
