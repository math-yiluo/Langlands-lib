# `Ш²` of the roots of unity over an open subgroup of `G_S`

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/KummerShaOpen.lean`, namespace `Langlands.GaloisCohomology`.

Let `L ⊆ K_S` be a finite extension of `K`, `P = G_S(L)` the open subgroup of `G_S` fixing `L`,
which is `G_{S_L}(L)` (`fixingOpenSubgroupEquiv`), and `μ_ℓ = μ_ℓ(K_S) = μ_ℓ(L_{S_L})`. The localization
of `P` is the Mackey family of the localization of `G_S` (`mackeyFamily P (localFamily ι S)`): its local
groups are the decomposition groups of the places of `L` above `S` (`mackeyPlaceEquiv`,
`mackeyLocalEquiv`), up to conjugation in `G_{S_L}(L)`
(`exists_fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom`). Transporting along these
identifications (`resRootsOfUnityHom`, `resMaximalSUnitsHom`):

* a class of `Hⁿ(P, μ_ℓ)` vanishes on the Mackey family exactly when its image in
  `Hⁿ(G_{S_L}(L), μ_ℓ)` vanishes at the places of `L` above `S`
  (`map_mackeyFamily_eq_zero_iff_localization`);
* for `n = 2`, `ℓ` prime and `ℓ` odd or `L` totally complex, this happens exactly when the class
  is the image of `H¹(P, 𝒪_Sˣ)` under the Kummer connecting map
  (`mem_shaSubmodule_mackey_iff_exists_kummerModNHom`), by `Ш²_{S_L}(L, μ_ℓ)` of `KummerSha.lean`.

```lean
theorem map_mackeyFamily_eq_zero_iff_localization (n : ℕ)
    (p : MackeyIndex (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (localFamily ι S))
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) n) :
    (map (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (localFamily ι S) p)
        (𝟙 _) n).hom y = 0 ↔
      localization ιL (dualizingModule L Ω (finitePlacesAbove L S) N)
        (Langlands.Galois.localPlace hL ι p.1 p.2.out).1 n
          ((rootsOfUnityTransport hL N n).hom y) = 0
theorem mem_shaSubmodule_mackey_iff_coeffMap_eq_zero (hN : N.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : N ≠ 2 ∨ IsTotallyComplex L)
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) 2) :
    y ∈ shaSubmodule (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (localFamily ι S)) (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (dualizingModule K Ω S N)) 2 ↔
      (coeffMap ((Rep.resFunctor (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype).map
          (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N)) 2).hom y = 0
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.map_mackeyFamily_eq_zero_iff_localization : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (N : ℕ)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ιL : Langlands.Galois.PlaceEmbeddings L Ω) [inst_10 : IsGalois L Ω]
  (n : ℕ)
  (p :
    Langlands.GaloisCohomology.MackeyIndex (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
      (Langlands.GaloisCohomology.PoitouTate.localFamily ι S))
  (y :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))
        n)),
  (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map
            (Langlands.GaloisCohomology.mackeyFamily
              (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
              (Langlands.GaloisCohomology.PoitouTate.localFamily ι S) p)
            (CategoryTheory.CategoryStruct.id
              (Rep.res
                (↑(Langlands.GaloisCohomology.mackeyFamily
                    (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
                    (Langlands.GaloisCohomology.PoitouTate.localFamily ι S) p))
                (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))))
            n))
        y =
      0 ↔
    (Langlands.GaloisCohomology.localization ιL
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule L Ω (Langlands.Galois.finitePlacesAbove L S) N)
          (↑(Langlands.Galois.localPlace hL ι (↑p.fst) (Quotient.out p.snd))) n)
        ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.rootsOfUnityTransport hL N n)) y) =
      0
@Langlands.GaloisCohomology.mem_shaSubmodule_mackey_iff_coeffMap_eq_zero : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (N : ℕ)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [inst_10 : NeZero N],
  Nat.Prime N →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) →
      N ≠ 2 ∨ NumberField.IsTotallyComplex L →
        ∀
          (y :
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))
                2)),
          y ∈
              Langlands.GaloisCohomology.shaSubmodule
                (Langlands.GaloisCohomology.mackeyFamily
                  (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
                  (Langlands.GaloisCohomology.PoitouTate.localFamily ι S))
                (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                  (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N))
                2 ↔
            (ModuleCat.Hom.hom
                  (Langlands.ProfiniteCohomology.coeffMap
                    ((Rep.resFunctor
                          (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype).map
                      (Langlands.GaloisCohomology.rootsOfUnityToSUnits S
                        (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) N))
                    2))
                y =
              0
```

## Outline of the proofs

Transport along `P ≅ G_{S_L}(L)` and `μ_N(K_S) = μ_N(L_{S_L})`. For a local group of the Mackey family, conjugation by the representative `x` followed by the isomorphism to `G_{S_L}(L)` is the localization of `L` at the corresponding place `w`, up to an inner automorphism (`exists_fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom`); inner automorphisms act trivially on cohomology, and restriction along an isomorphism is injective (`injective_map_of_continuousMulEquiv` of the module `Langlands.Cohomology.Profinite.ClassFormation.Basic`, and `injective_coeffMap_of_bijective` of `Langlands.Cohomology.Profinite.Duality.DualModule` for the coefficients). The places `w` exhaust `S_L` (`mackeyPlaceEquiv`), so vanishing on the Mackey family is vanishing in `Ш²_{S_L}(L, μ_ℓ)`, which `KummerSha` computes.

- `map_mackeyFamily_eq_zero_iff_localization`: **The local groups of `P`.** Restriction along the Mackey family at `p` vanishes on a class of `Hⁿ(P, μ_N)` exactly when the localization at the place `w` of `L` attached to `p` vanishes on its transport to `G_{S_L}(L)`.
- `mem_shaSubmodule_mackey_iff_coeffMap_eq_zero`: **`Ш²` of `μ_ℓ` over `P = G_S(L)`.** For a prime `ℓ = N` with the places above `ℓ` in `S`, and `ℓ` odd or `L` totally complex, a class of `H²(P, μ_ℓ)` vanishes on the Mackey family of `P` exactly when its image in `H²(P, 𝒪_Sˣ)` vanishes.

## Declarations

`fixingOpenSubgroupEquivSymm`, `resRootsOfUnityHom`, `resRootsOfUnityHom_hom_apply`, `resRootsOfUnityHom_bijective`, `resRootsOfUnityHom_comp_rootsOfUnityToSUnits`, `rootsOfUnityTransport`, `coeffMap_rootsOfUnityTransport`, `injective_map_resMaximalSUnitsHom`, `bijective_rootsOfUnityTransport`, `isSmoothRep_res_mackeyFamily_dualizingModule`, `conjLocalizationHom`, `transportModule`, `isSmoothRep_transportModule`, `map_eq_zero_iff_localization_of_comp`, `map_mackeyFamily_eq_zero_iff_localization`, `mem_shaSubmodule_mackey_iff`, `mem_shaSubmodule_mackey_iff_coeffMap_eq_zero`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 506 ((iii) over the extension K).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/KummerShaOpen.lean` lines 137–191. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `mem_ptSha_mackey_iff` → `mem_shaSubmodule_mackey_iff`, `gsRootsOfUnityIso_symm_comp_rootsOfUnityToSUnits` → `resRootsOfUnityHom_comp_rootsOfUnityToSUnits`, `cohomologyMap_rootsOfUnityToSUnits_gsRootsOfUnityCohomologyIso` → `coeffMap_rootsOfUnityTransport`, `mem_ptSha_mackey_iff_exists_kummerModN` → `mem_shaSubmodule_mackey_iff_coeffMap_eq_zero`.
