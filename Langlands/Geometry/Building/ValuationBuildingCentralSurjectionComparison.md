# Reduced buildings along a central surjection

Module `Langlands.Geometry.Building.ValuationBuildingCentralSurjectionComparison`.

Over a nonarchimedean local field `F`, this module proves the first comparison
clause of `BuildingComparisonAxiomStatement`.
`exists_isEquivariantBuildingIso_centralSurjection f hf B B'` states: for
`f : G → G'` with `IsCentralSurjection f` and arbitrary
`B : ValuationBuildingData G` and `B' : ValuationBuildingData G'`, there is
`Φ : B.ReducedBuilding ≃ B'.ReducedBuilding` with
`IsEquivariantBuildingIso B B' (rationalPoints.map f) Φ`. The kernel of `f` may
contain a torus, as for `GL_n → PGL_n`. The proof therefore passes through
the derived subgroups, where `f` restricts to a central isogeny.

## Centralizer map

Section `CentralizerMap`: let `i : S → G` and `i' : S' → G'` be tori,
`f : G → G'`, and `fS : S → S'` flat and surjective with `i ≫ f = fS ≫ i'`.
Let `CS`, `CT` be centralizer data of `i` and `i'`.

- `range_centralizer_comp_le_of_flat`: `f` maps the centralizer `Z` of `S`
  into the centralizer `Z'` of `S'`
  (`TorusCoverTransport.map_mem_torusCentralizer`).
- `centralizerMapOfFlat : CS.Z ⟶ CT.Z` is the induced map, with
  `centralizerMapOfFlat_comp` (`fZ ≫ j' = j ≫ f`) and
  `centralizerMapOfFlat_torus` (`s ≫ fZ = fS ≫ s'`).
- `centralizerMapOfFlat_translation`: the translation vectors of V 6 satisfy
  `fS_*(ν(z)) = ν'(fZ(z))`. This is the Library's
  `cocharacterMapReal_centralizerTranslation`.

These follow the Library's `centralIsogenyCentralizerMap`, which needs an
isogeny `fS`. Here only flatness and surjectivity of `fS` are used.

## Reduction to derived data

`exists_isEquivariantBuildingIso_of_derivedIsogeny` takes the following
hypotheses:

- `f : G → G'` flat and surjective;
- data `B`, `B'`, and `fS : B.S → B'.S` flat, surjective and locally of
  finite presentation, with `B.i ≫ f = fS ≫ B'.i`;
- derived subgroups `d : D → G` and `d' : D' → G'`, and a central isogeny
  `fD : D → D'` with `fD ≫ d' = d ≫ f`;
- maximal split tori `j : T → D` and `j' : T' → D'`, with closed
  `e : T → B.S` and `e' : T' → B'.S` satisfying `j ≫ d = e ≫ B.i` and
  `j' ≫ d' = e' ≫ B'.i`;
- an isogeny `t : T → T'` with `j ≫ fD = t ≫ j'` and `t ≫ e' = e ≫ fS`.

It concludes that the reduced buildings of `B` and `B'` are identified along
`f`.

Proof. Choose central split components `c : A → B.S` and `c' : A' → B'.S`
(`splitComponentStatement`, `derivedCentralSplitTorusProduct`), as in
module `ValuationBuildingDerivedComparison`.

1. *One derived class.* Let `X` be the derived pullback of `B.apartment`
   through `d`. Let `Y` be the central-isogeny pullback through `fD` of the
   derived pullback `X'` of `B'.apartment` through `d'`. Both are
   apartment classes for `(D, j)` satisfying V 6 for the centralizer datum
   `CentralizerDatum.ofValuationComparison` of `j`
   (`IsOmegaCompatible.derivedPullback`,
   `IsOmegaCompatible.centralIsogenyPullback`). By KP Proposition 6.2.6
   (`omegaCompatibleApartmentUniqueness`), `X = Y`.
2. *Two comparisons.* Let `cd := derivedComparison` (from `X` to `B` along
   `d`). Let `cX` be `centralIsogenyComparison` followed by
   `derivedComparison` (from `Y` to `B'` along `d' ∘ fD`), moved to the source
   `X` by `Comparison.congrLeft`. The apartment map is
   `E := cd.e⁻¹ ≫ cX.e : A(B) ≃ᵃ A(B')`. Since `fD ≫ d' = d ≫ f`,
   `map d' ∘ map fD = map f ∘ map d` (`hθ`).
3. *Linear part.* `E.linear [w] = [fS_* w]` for every `w ∈ V(S)` (`hlin`).
   Write `w = e_* v + c_* z` (`exists_eq_cocharacterMapReal_add_of_centralComplement`).
   The central part `c_* z` is annihilated by the roots of `S`
   (`root_restrict_eq_zero_of_isCentral`). Its image `fS_* c_* z` is
   annihilated by the roots of `S'`, because `c ≫ B.i ≫ f` is central
   (`IsCentral.comp_flat_surjective`). On `e_* v` the linear parts are the
   quotient maps of the cocharacter maps (`derivedTranslationEquiv`,
   `centralIsogenyTranslationEquiv`). The identity `t ≫ e' = e ≫ fS` then
   gives `e'_* t_* v = fS_* e_* v` (`cocharacterMapReal_comp`).
4. *The transfer along `f`.* The `KPApartmentData.Transfer` from
   `B.apartment` to `B'.apartment` along `rationalPoints.map f` has the
   following parts:
   - *Normalizers:* `f(N(F)) ⊆ N'(F)` by
     `TorusCoverTransport.normalizerPointsMap` for `fS`.
   - *Equivariance:* by Fact 2.6.22 (`simplyConnectedCentralizerProduct`,
     with a simply connected cover of `D`), write `n ∈ N(F)` as
     `n = d(m) · z` with `z` in the centralizer `Z(F)`. Then
     `m ∈ N_D(T)(F)` (`DerivedCoverNormalizerLift.mem_normalizerPoints` for
     `𝟙 D`).
     - For `d(m)`, equivariance is that of `cd` and `cX`
       (`Comparison.e_symm_smul`, `e_smul`).
     - For `z`, V 6 (`IsOmegaCompatible.smul_eq_vadd`) makes `z` and `f(z)`
       act by the translations `ν(z)` and `ν'(fZ z)`. These correspond under
       `E` by step 3 and `centralizerMapOfFlat_translation`.
   - *Sharp fixers:* `f(G(F)^♯_{cd.e y}) = f(d(D(F)^♯_y)) = G'(F)^♯_{cX.e y}`,
     by `cd.map_sharpFixer`, `cX.map_sharpFixer` and `hθ`.
   - *Normalizer reflection:* write `g = d(m) · n₀` with `n₀ ∈ N(F)`
     (`exists_eq_map_mul_normalizer`). If `f(g) ∈ N'(F)`, then
     `d'(fD(m)) = f(d(m)) ∈ N'(F)`. So `m ∈ N_D(T)(F)` by
     `DerivedCoverNormalizerLift.mem_normalizerPoints` for `fD` and `d'`,
     and `g ∈ N(F)`.
   - *Surjectivity:* `G'(F) = (π' ≫ d')(C'(F)) · N'(F)` by Fact 2.6.22 for a
     simply connected cover `π'` of `D'`. By the universal property of `π'`
     (`IsSimplyConnectedCover.universal`) for the central isogeny `fD`,
     `π' = λ ≫ fD`. So `(π' ≫ d')(c) = f(d(λ(c)))`.
   - *Roots:* `transportedRoots_trans`, `transportedRoots_symm` and the root
     identities of `cd` and `cX`.

   `Transfer.isEquivariantBuildingIso` gives the isomorphism.

## Assembly

`exists_isEquivariantBuildingIso_centralSurjection` supplies the reduction's
hypotheses. `f` is flat by `flat_of_surjective`. The group-scheme inputs come
from module `Langlands.GroupScheme.CentralSurjection.TorusImage`:

- `exists_maximalSplitTorus_image` gives the image torus `i' : S' → G'` and
  `fS`.
- `IsDerivedSubgroup.isCentralIsogeny_map` (module `…CentralSurjection.DerivedMap`)
  shows that the induced map `fD := hd.map hd' f` of the derived subgroups
  from `derivedSubgroupRepresentability` is a central isogeny, with
  `IsDerivedSubgroup.map_comp`.
- `derivedMaximalSplitTorus` gives `j`, `e` and `j'`, `e'`.
- `exists_derivedTorus_isogeny` gives `t`.

The datum `B'` has an arbitrary torus. `maximalSplitTorusConjugacy` gives
`g ∈ G'(F)` conjugating its torus onto `i'`.
`ValuationBuildingData.basedTransport` along the inner automorphism of `g`
gives data `B''` with torus `i'`. The reduction applies to `B` and `B''`, and
`IsEquivariantBuildingIso.exists_retarget` (module
`ValuationBuildingSameGroupComparison`) passes to `B'`.

## Provenance

The theorem is clause (1) of the Library statement
`BuildingComparisonAxiomStatement`, which records the source: Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Axiom 4.1.1 (printed
pp.157–158), (7.6.1) and Remark 7.6.5 (printed pp.264, 266). The route
through derived subgroups, the use of V 6 for the centralizer, and the
quotient comparison are this development's. KP's Proposition 6.2.6 and
Fact 2.6.22 enter through `omegaCompatibleApartmentUniqueness` and
`simplyConnectedCentralizerProduct`.
