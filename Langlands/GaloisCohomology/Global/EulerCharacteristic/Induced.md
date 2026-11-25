# Shapiro's lemma for the Euler characteristic ratio

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Induced.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a Galois extension, `S` a set of finite places of `K`, `G_S` the Galois
group of `K_S ⊆ Ω`, `ι : PlaceEmbeddings K Ω`, and `L` a number field with `K → L → Ω` and `L ⊆ K_S`;
let `U ⊆ G_S` be the open subgroup fixing `L`, identified with `G_{S_L}(L)` for the places `S_L` of
`L` above `S` (`fixingOpenSubgroupEquiv`). For a finite smooth `U`-module `B`, viewed as a
`G_{S_L}(L)`-module (`resFixedField`), and any `ιL : PlaceEmbeddings L Ω`,

`globalEulerRatio ι (Ind_U^{G_S} B) = globalEulerRatio ιL B` (`globalEulerRatio_coind`).

The Euler characteristics agree by Shapiro's lemma (`eulerCharacteristic_coind`) and the
identification `U ≅ G_{S_L}(L)`. At a real place `v` of `K`, Mackey's formula
(`mackeyCohomologyEquiv`) splits `H⁰(K_v, Ind B)` over the double cosets `U \ G_S / G_v`, which are the
infinite places of `L` above `v` (`Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.InducedPlaces`);
the factor of a double coset is `#H⁰(L_w, B)` (`card_cohomology_zero_mackeyRep`). So
`∏_{v real} #H⁰(K_v, Ind B) = ∏_{w real} #H⁰(L_w, B) · #B^c` with `c` the number of complex places of
`L` above real places of `K`, and `#∞_L + c = [L:K] · #∞_K`
(`card_infinitePlace_add_card_complex_over_real`) accounts for `#Ind B = #B^{[L:K]}`.

```lean
theorem prod_prod_fiber_eq (f : InfinitePlace L → ℕ) (c : ℕ) (hf : ∀ w, w.IsComplex → f w = c) :
    ∏ v : {v : InfinitePlace K // v.IsReal},
        ∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v.1}, f w.1 =
      (∏ w : {w : InfinitePlace L // w.IsReal}, f w.1) *
        c ^ (Finset.univ.filter fun w : InfinitePlace L =>
          w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal).card
theorem globalEulerRatio_coind [Finite B] :
    globalEulerRatio ι (Rep.coind (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype B) =
      globalEulerRatio ιL (resFixedField hL B)
theorem globalEulerRatio_coind_res (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep M] [Finite M] :
    globalEulerRatio ι (Rep.coind (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) =
      globalEulerRatio ιL (resToFixedField hL M)
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.prod_prod_fiber_eq : ∀ {K L : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L] (f : NumberField.InfinitePlace L → ℕ) (c : ℕ),
  (∀ (w : NumberField.InfinitePlace L), w.IsComplex → f w = c) →
    ∏ v : { v : NumberField.InfinitePlace K // v.IsReal },
        ∏ w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = ↑v }, f ↑w =
      (∏ w : { w : NumberField.InfinitePlace L // w.IsReal }, f ↑w) *
        c ^ {w : NumberField.InfinitePlace L | w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal}.card
@Langlands.GaloisCohomology.globalEulerRatio_coind : ∀ {K L Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Field Ω] [inst_5 : Algebra K L] [inst_6 : Algebra K Ω]
  [inst_7 : Algebra L Ω] [inst_8 : IsScalarTower K L Ω] [inst_9 : IsGalois K Ω] [inst_10 : IsGalois L Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ιL : Langlands.Galois.PlaceEmbeddings L Ω)
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) ↥↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
  [inst_11 : Langlands.IsSmoothRep B] [Finite ↑B],
  Langlands.GaloisCohomology.globalEulerRatio ι
      (Rep.coind.{u, u, u, u} (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype B) =
    Langlands.GaloisCohomology.globalEulerRatio ιL (Langlands.GaloisCohomology.resFixedField hL B)
@Langlands.GaloisCohomology.globalEulerRatio_coind_res : ∀ {K L Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Field Ω] [inst_5 : Algebra K L] [inst_6 : Algebra K Ω]
  [inst_7 : Algebra L Ω] [inst_8 : IsScalarTower K L Ω] [inst_9 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_10 : IsGalois L Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ιL : Langlands.Galois.PlaceEmbeddings L Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_11 : Langlands.IsSmoothRep M] [Finite ↑M],
  Langlands.GaloisCohomology.globalEulerRatio ι
      (Rep.coind.{u, u, u, u} (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
        (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype M)) =
    Langlands.GaloisCohomology.globalEulerRatio ιL (Langlands.GaloisCohomology.resToFixedField hL M)
```

## Outline of the proofs

Shapiro's lemma identifies `H^i(G_S, Ind_U B)` with `H^i(U, B)`, and `U ≅ G_{S_L}(L)` transports this to `L`. At a real place `v` of `K`, Mackey's formula decomposes `H⁰(K_v, Ind B)` as a product over `U \ G_S / G_v`; a double coset with full Mackey subgroup is a real place `w` of `L` and contributes `#H⁰(L_w, B)`, the others contribute `#B`. Counting places (`#∞_L + c = [L:K]·#∞_K`) and `#Ind B = #B^{[L:K]}` gives the equality of the ratios.

- `prod_prod_fiber_eq`: **Regrouping a product over the infinite places.** For `f` on the infinite places of `L` with value `c` at the complex places, the product of `f` over the places above the real places of `K` is the product over the real places of `L` times `c` to the number of complex places of `L` above real places of `K`.
- `globalEulerRatio_coind`: **Shapiro's lemma for the Euler characteristic ratio.** For a finite smooth module `B` of the subgroup `U ⊆ G_S` fixing `L`, the ratio of `Ind_U^{G_S} B` for `K` is the ratio of `B` for `L`.
- `globalEulerRatio_coind_res`: **Shapiro's lemma for the ratio**, for a module of `G_S`: the ratio of `Ind_U^{G_S} Res_U M` for `K` is the ratio of `M` as a `G_{S_L}(L)`-module.

## Declarations

`index_fixingOpenSubgroup`, `finiteIndex_fixingOpenSubgroup`, `card_coind_fixingOpenSubgroup`, `liesOver_of_comap_eq`, `card_fiber_add_card_complex_eq_finrank`, `card_infinitePlace_add_card_complex_over_real`, `fixingOpenSubgroupInvHom`, `fixingOpenSubgroupInvHom_apply`, `resFixedField`, `isSmoothRep_resFixedField`, `card_cohomology_resFixedField`, `eulerCharacteristic_resFixedField`, `card_cohomology_zero_eq_card_invariants`, `card_cohomology_zero_mackeyRep`, `card_cohomology_zero_realLocalModule_coind`, `prod_prod_fiber_eq`, `prod_card_cohomology_zero_coind`, `globalEulerRatio_coind`, `resToFixedField`, `resToFixedField_ρ_apply`, `isSmoothRep_resToFixedField`, `finite_resToFixedField`, `card_resToFixedField`, `globalEulerRatio_coind_res`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 507 (φ(G_S, Ind_U A) = φ(U, A) by Shapiro's lemma and the decomposition at the real places).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShapiroDefs.lean` lines 1–32, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShapiroCoind.lean` lines 1–223, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShapiroRatio.lean` lines 1–131, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShapiroReal.lean` lines 1–180, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/CardCohomologyZeroMackeyRepOfNeTop.lean` lines 1–95, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/Shapiro.lean` lines 1–33. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `card_coind_eq` → `card_coind_fixingOpenSubgroup`, `eulerChar_res_continuousMulEquiv` → `eulerCharacteristic_resFixedField`, `prod_gsRealH0Card_coind` → `prod_card_cohomology_zero_coind`, `ratio_coind_arith` → `globalEulerRatio_coind`, `gsEulerRatio_coind_eq_of` → `globalEulerRatio_coind`, `index_gsOpenSubgroup` → `index_fixingOpenSubgroup`, `finiteIndex_gsOpenSubgroup` → `finiteIndex_fixingOpenSubgroup`, `card_coind_gsOpenSubgroup` → `card_coind_fixingOpenSubgroup`, `count_places_arith` → `card_infinitePlace_add_card_complex_over_real`, `card_infinitePlace_eq_real_add_complex` → `card_infinitePlace_add_card_complex_over_real`, `card_infinitePlace_add_card` → `card_fiber_add_card_complex_eq_finrank`, `gsRealH0Card_coind` → `card_cohomology_zero_realLocalModule_coind`, `card_cohomology_zero_mackeyRep_of_ne_top` → `card_cohomology_zero_mackeyRep`, `card_cohomology_zero_mackeyRep_top` → `card_cohomology_zero_mackeyRep`, `exists_gsEulerRatio_coind_eq` → `globalEulerRatio_coind_res`.
