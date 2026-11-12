# Root groups meet the zero fixers in the root fixers (KP Axiom 4.1.8 (3))

Module `Langlands.Geometry.Building.RootGroupZeroFixer` states and proves
part (3) of Kaletha–Prasad Axiom 4.1.8 for the building of KP Chapter 7 on
supplied data `P : ParahoricBuildingData G` over a nonarchimedean local field
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, 2023: Axiom 4.1.8,
printed p.160 / PDF p.191; 4.1.28, printed p.166 / PDF p.197; Lemma 7.7.3,
printed p.268 / PDF p.299). It also proves
`P_Ω ⊆ G(F)^0_Ω`, which gives one inclusion of part (2).

## Statement

`RootZeroFixersStatement.{u}`: for every nonarchimedean local field
`F : Type u`, group scheme `G` over `F` with `[IsAffineHom G.X.hom]` and
`P : ParahoricBuildingData G` with `P.SatisfiesApartmentAxioms` (V 7 and
AS 2–AS 5; V 6 is part of the data), `P.HasRootZeroFixers` holds: for every
non-empty bounded `Ω ⊆ A(S)` and every relative root `a`,

```
P.rootGroup a ⊓ P.zeroFixer Ω = P.rootFixer a Ω
```

that is, `U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}`. Here `P.zeroFixer Ω` is the group
of elements of `G(F)^0` fixing the image of `Ω` in the reduced building
pointwise, and `P.rootFixer a Ω = U_a(F) ∩ ⋂_{x ∈ Ω} U_{a,x,0}`. The theorem
`rootZeroFixers` proves the statement. It is the second conjunct of the
published `RootGroupActionAxiomStatement`.

## Implemented proof

1. `parahoric_le_zeroFixer`: `P.parahoric Ω ≤ P.zeroFixer Ω` for every `Ω`.
   The parahoric lies in `G(F)^0` by `ParahoricBuildingData.parahoric_le_zeroSubgroup`
   (module `ApartmentRootCover`). For `x ∈ Ω` it fixes the image of `x`, by
   `ParahoricBuildingData.parahoric_le_compactStabilizer` (module
   `KPParahoricFixerComparison`, using V 7) and
   `KPApartmentData.mem_compactStabilizer`. Composing with the published
   `nonnegativeRootSubgroup_le_parahoric` gives
   `nonnegativeRootSubgroup_le_zeroFixer`, the inclusion `⊇` of KP
   Axiom 4.1.8 (2).
2. `mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq`: let
   `ν` be a generic cocharacter and let `g` be in the positive unipotent group
   of `ν` and fix the image of `x`. `ApartmentQuotient.mem_stabilizer_apartment_iff`
   writes `g = s · m` with `s ∈ G(F)^♯_x` and `m ∈ N(F)` fixing `x`. Point
   exchange (`ValuationBuildingData.sharpFixer_subset_mul_sharpNormalizerStabilizer`
   for `-ν`) writes `s = v · w · n` with `v` in the positive and `w` in the
   negative depth-zero chamber root groups at `x` and `n ∈ N(F)`. Then
   `n m = w⁻¹ (v⁻¹ g)` is a normalizer element in the product of the opposite
   and the positive unipotent groups, so it is `1`
   (`normalizer_eq_one_of_unipotent_product`). Then `w = v⁻¹ g` lies in both
   unipotent groups, so `w = 1`
   (`Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`). Hence `g = v`.
   This follows the published
   `ParahoricBuildingData.mem_positiveRootGroups_of_mem_unipotent_of_mem_parahoric`
   (module `PointParahoricRootIntersection`), with its `Z(F)^0` factor
   replaced by the normalizer factor `m`. This is KP's Bruhat argument in
   the proof of Lemma 7.7.3.
3. `mem_filtration_of_mem_rootGroup_of_smul_apartmentMap_eq`: an element of
   `U_a(F)` fixing the image of `x` lies in `U_{a,x,0}`. Choose a generic
   cocharacter `ν` with `⟨a, ν⟩ > 0`
   (`exists_genericCocharacter`, negated if needed). Then `g` lies in the
   positive unipotent group of `ν` (`RelativeRoot.subgroup_le_dynamicUnipotent`),
   step 2 applies, and the published
   `KPApartmentData.mem_filtration_of_mem_rootGroup_of_mem_positiveRootGroups`
   isolates the coordinate at `a`. The rank-one input is
   `Langlands.GroupScheme.rootRankOneFactorization` and the ordered-product
   input is `RelativeRoot.dynamicRootOrderedProduct`, both proved in the
   Library.
4. `rootGroup_inf_zeroFixer_eq_rootFixer`: for every `Ω` (empty or
   unbounded allowed), `U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}`. The inclusion `⊆`
   applies step 3 at each `x ∈ Ω`, using `mem_zeroFixer`. The inclusion `⊇`
   is `P.rootFixer_le_parahoric` followed by step 1.
5. `hasRootZeroFixers` restricts step 4 to non-empty bounded `Ω`, and
   `rootZeroFixers` proves the statement.

## Provenance and scope

The statement is the part (3) clause of the published
`RootGroupActionAxiomStatement` (KP Axiom 4.1.8 (3)). The 2024 corrections to
KP emphasize that `Ω` is non-empty and bounded in Axiom 4.1.8 (2) (PDF p.27),
and the published statement uses the same `Ω` in part (3); they also make
Chapter 7 assume AS 5 (PDF p.33). The proof is derived from Library definitions and
proved theorems and adds no hypotheses or axioms. It proves only the
inclusion `⊇` of part (2), not part (2) itself.
