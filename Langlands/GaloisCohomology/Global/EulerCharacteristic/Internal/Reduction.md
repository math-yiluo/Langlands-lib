# Reduction of the Euler characteristic formula to extensions of degree prime to `ℓ`

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Reduction.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places containing the
places above a prime `ℓ`, and `G_S` the Galois group of `K_S ⊆ Ω`. For an open subgroup
`W = G_S(L')` let `χ_W(X) = globalEulerRatio ι (Ind_W^{G_S} X)` for finite smooth `W`-modules `X`.

* `χ_W` is multiplicative on `ℓ`-primary modules (`isMultiplicativeOn_ratio_coind`), so for an open
  normal subgroup `V ⊆ W` with `W/V` cyclic of order `ℓ^a` and `M` killed by `ℓ`,
  `ratio(Ind_V M) = ratio(Ind_W M)^{ℓ^a}` (`globalEulerRatio_coind_stage_pow`), by
  `IsMultiplicativeOn.coind_res_eq_pow` and transitivity of induction (`nonempty_coind_coind_iso`).
* A cyclic quotient `W/U` splits as an `ℓ`-part `W/V` and a part `V/U` of order prime to `ℓ`
  (`exists_coprime_part`).
* Hence, with Shapiro's lemma (`globalEulerRatio_coind`), the formula for `Ind_W M`, `W/U` cyclic,
  follows from the formula over the fixed field `K''` of `V` for `M` viewed as a `G_S(K'')`-module, where
  now `[L : K'']` is prime to `ℓ` (`globalEulerRatio_coind_eq_one`).

```lean
theorem exists_coprime_part (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (U W : Subgroup G) [hN : U.Normal]
    (hUi : U.index ≠ 0) (hle : U ≤ W) (hcyc : IsCyclic (W ⧸ U.subgroupOf W)) :
    ∃ V : Subgroup G, U ≤ V ∧ V ≤ W ∧ IsCyclic (V ⧸ U.subgroupOf V) ∧
      Nat.Coprime (U.subgroupOf V).index ℓ ∧
      ∃ hnorm : (V.subgroupOf W).Normal,
      (haveI
theorem globalEulerRatio_coind_stage_pow {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W V : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) (hle : V ≤ W)
    [hN : ((V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf W).Normal]
    [hc : IsCyclic (W ⧸ (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf W)] {a : ℕ}
    (hcard : Nat.card (W ⧸ (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf W) = ℓ ^ a)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hℓM : ∀ m : M, ℓ • m = 0) :
    globalEulerRatio ι (Rep.coind (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (Rep.res (V : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) =
      globalEulerRatio ι (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) ^
        (ℓ ^ a)
theorem globalEulerRatio_coind_eq_one {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    [(U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hℓM : ∀ m : M, ℓ • m = 0)
    (hK : ∀ (K'' : IntermediateField K Ω) [NumberField K'']
      (hK'' : ∀ x : K'', algebraMap K'' Ω x ∈ maximalUnramifiedOutside K Ω S),
      (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
        GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' →
      IsCyclic ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
        (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
          (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S))) →
      Nat.Coprime ((U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S))).index ℓ →
      ∀ ιK'' : PlaceEmbeddings K'' Ω, globalEulerRatio ιK'' (resToFixedField hK'' M) = 1)
    (W : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    (hle : (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤ W)
    [((U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
      (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S))).Normal]
    (hcyc : IsCyclic ((W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ⧸
      (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
        (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))) :
    globalEulerRatio ι (Rep.coind (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (Rep.res (W : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) = 1
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.exists_coprime_part : ∀ {G : Type u_1} [inst : Group G] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
  (U W : Subgroup G) [hN : U.Normal],
  U.index ≠ 0 →
    U ≤ W →
      IsCyclic (↥W ⧸ U.subgroupOf W) →
        ∃ (V : Subgroup G),
          U ≤ V ∧
            V ≤ W ∧
              IsCyclic (↥V ⧸ U.subgroupOf V) ∧
                (U.subgroupOf V).index.Coprime ℓ ∧
                  ∃ (hnorm : (V.subgroupOf W).Normal),
                    IsCyclic (↥W ⧸ V.subgroupOf W) ∧ ∃ (a : ℕ), Nat.card (↥W ⧸ V.subgroupOf W) = ℓ ^ a
@Langlands.GaloisCohomology.globalEulerRatio_coind_stage_pow : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ (W V : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)),
      V ≤ W →
        ∀ [hN : ((↑V).subgroupOf ↑W).Normal] [hc : IsCyclic (↥W ⧸ (↑V).subgroupOf ↑W)] {a : ℕ},
          Nat.card (↥W ⧸ (↑V).subgroupOf ↑W) = ℓ ^ a →
            ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
              [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
              (∀ (m : ↑M), ℓ • m = 0) →
                Langlands.GaloisCohomology.globalEulerRatio ι
                    (Rep.coind.{u, u, u, u} (↑V).subtype (Rep.res (↑V).subtype M)) =
                  Langlands.GaloisCohomology.globalEulerRatio ι
                      (Rep.coind.{u, u, u, u} (↑W).subtype (Rep.res (↑W).subtype M)) ^
                    ℓ ^ a
@Langlands.GaloisCohomology.globalEulerRatio_coind_eq_one : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [inst_6 : (↑U).Normal]
      (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_7 : Langlands.IsSmoothRep M] [Finite ↑M],
      (∀ (m : ↑M), ℓ • m = 0) →
        (∀ (K'' : IntermediateField K Ω) [inst_9 : NumberField ↥K'']
            (hK'' : ∀ (x : ↥K''), (algebraMap (↥K'') Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
            ↑U ≤ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'') →
              IsCyclic
                  (↥↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'') ⧸
                    (↑U).subgroupOf ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'')) →
                ((↑U).subgroupOf
                          ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'')).index.Coprime
                    ℓ →
                  ∀ (ιK'' : Langlands.Galois.PlaceEmbeddings (↥K'') Ω),
                    Langlands.GaloisCohomology.globalEulerRatio ιK''
                        (Langlands.GaloisCohomology.resToFixedField hK'' M) =
                      1) →
          ∀ (W : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)),
            ↑U ≤ ↑W →
              ∀ [inst_9 : ((↑U).subgroupOf ↑W).Normal],
                IsCyclic (↥↑W ⧸ (↑U).subgroupOf ↑W) →
                  Langlands.GaloisCohomology.globalEulerRatio ι
                      (Rep.coind.{u, u, u, u} (↑W).subtype (Rep.res (↑W).subtype M)) =
                    1
```

## Outline of the proofs

Write a cyclic `W/U` as `W/V × V/U` with `W/V` an `ℓ`-group and `V/U` of order prime to `ℓ`. Multiplicativity of `χ_W` on `ℓ`-primary modules and the filtration lemma give `ratio(Ind_V M) = ratio(Ind_W M)^{ℓ^a}`; a positive rational whose `ℓ^a`-th power is `1` is `1`. Shapiro's lemma turns `ratio(Ind_V M)` into the ratio of `M` over the fixed field of `V`.

- `exists_coprime_part`: **The `ℓ`-part of a cyclic quotient.** For open subgroups `U ≤ W` of finite index with `U` normal and `W/U` cyclic, there is `U ≤ V ≤ W` with `V/U` cyclic of order prime to `ℓ`, `V` normal in `W` and `W/V` cyclic of order a power of `ℓ`.
- `globalEulerRatio_coind_stage_pow`: **The `ℓ`-part of an induction.** For `V ⊆ W` open with `W/V` cyclic of order `ℓ^a` and `M` killed by `ℓ`, `ratio(Ind_V M) = ratio(Ind_W M)^{ℓ^a}`.
- `globalEulerRatio_coind_eq_one`: **Induction from a cyclic quotient.** Let `U = G_S(L) ⊆ W = G_S(L')` with `U` normal and `W/U` cyclic, and `M` killed by `ℓ`. If the formula holds over every field `K''` with `U ⊆ G_S(K'')`, `G_S(K'')/U` cyclic of order prime to `ℓ`, for `M` viewed as a `G_S(K'')`-module, then it holds for `Ind_W M`.

## Declarations

`coindStagesEquiv`, `nonempty_coind_coind_iso`, `exists_coprime_part`, `exists_card_eq_pow_of_nsmul_prime`, `isMultiplicativeOn_ratio_coind`, `globalEulerRatio_coind_stage_pow`, `globalEulerRatio_coind_eq_one`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 508 (reduction to a cyclic extension of degree prime to p trivializing A).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkKilledB.lean` lines 1–347, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/ExistsPrimeToPart.lean` lines 1–127. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `coind_stages` → `coindStagesEquiv`, `ratio_coind_stage_pow` → `globalEulerRatio_coind_stage_pow`, `exists_prime_to_part` → `exists_coprime_part`, `exists_ratio_coind_eq_resTo` → `globalEulerRatio_coind_eq_one`, `ratio_coind_cyclic` → `globalEulerRatio_coind_eq_one`, `exists_prime_to_part` → `exists_coprime_part`.
