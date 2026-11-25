# Multiplicativity of the Euler characteristic ratio of `G_S`

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Multiplicative.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K` and
`ι : PlaceEmbeddings K Ω`. For a short exact sequence `0 → A → B → C → 0` of finite smooth
`G_S`-modules, the long exact cohomology sequence, cut after `H²`, gives

`χ(A) · χ(C) = χ(B) · #ker(H³(G_S, A) → H³(G_S, B))`
(`eulerCharacteristic_mul_eq_mul_card_ker`),

and at a real place `w`, where `χ(K_w, ·) = #H⁰(K_w, ·)` for finite modules,

`#H⁰(K_w, A) · #H⁰(K_w, C) = #H⁰(K_w, B) · #ker(H³(K_w, A) → H³(K_w, B))`.

When the localization `H³(G_S, ·) → ∏_{w real} H³(K_w, ·)` is bijective for `A` and injective for
`B`, the two kernels correspond, and the ratio `globalEulerRatio` of
`Langlands.GaloisCohomology.Global.EulerCharacteristic.Ratio` is multiplicative
(`globalEulerRatio_shortExact_of_bijective`). Tate's theorem on the real places in degree three
(`realLocalizationDegreeThreeStatement` of `Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`)
provides this for every finite module with the places above its order in `S`
(`globalEulerRatio_shortExact`).

Consequences proved here:

* `globalEulerRatio_eq_one_of_primary`: if the ratio is `1` for every finite module killed by a prime
  `ℓ` (with the places above `ℓ` in `S`), it is `1` for every finite module killed by a power of `ℓ`
  (dévissage `0 → M[ℓ] → M → ℓM → 0`).
* `IsMultiplicativeOn` (functions of finite modules multiplicative on short exact sequences whose
  middle term has order in a class `P`) and `IsMultiplicativeOn.coind_res_eq_pow`: for an open normal
  subgroup `H` with cyclic quotient of order `p^a` and a module killed by `p`, the value on
  `Ind_H^G Res_H M` is the `p^a`-th power of the value on `M`.

```lean
theorem globalEulerRatio_shortExact_of_bijective (hT : T.ShortExact) [Finite T.X₂]
    (hn : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card T.X₂ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hA : Function.Bijective fun (x : cohomology T.X₁ 3) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι T.X₁ w.1 3 x)
    (hB : Function.Injective fun (x : cohomology T.X₂ 3) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι T.X₂ w.1 3 x) :
    globalEulerRatio ι T.X₂ = globalEulerRatio ι T.X₁ * globalEulerRatio ι T.X₃
theorem globalEulerRatio_shortExact (hT : T.ShortExact) [Finite T.X₂]
    (hn : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card T.X₂ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    globalEulerRatio ι T.X₂ = globalEulerRatio ι T.X₁ * globalEulerRatio ι T.X₃
theorem globalEulerRatio_eq_one_of_primary {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (h : ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
      [Finite M], (∀ m : M, ℓ • m = 0) → globalEulerRatio ι M = 1)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    {r : ℕ} (hr : ∀ m : M, (ℓ ^ r) • m = 0) : globalEulerRatio ι M = 1
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.globalEulerRatio_shortExact_of_bijective : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {T :
    CategoryTheory.ShortComplex (Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))}
  [inst_5 : Langlands.IsSmoothRep T.X₁] [inst_6 : Langlands.IsSmoothRep T.X₂] [inst_7 : Langlands.IsSmoothRep T.X₃]
  [Finite ↑S],
  T.ShortExact →
    ∀ [Finite ↑T.X₂],
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          ↑(Nat.card ↑T.X₂) ∈ v.asIdeal → v ∈ S) →
        (Function.Bijective
            fun (x : ↑(Langlands.ProfiniteCohomology.cohomology T.X₁ 3))
              (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
            (Langlands.GaloisCohomology.realLocalization ι T.X₁ (↑w) 3) x) →
          (Function.Injective
              fun (x : ↑(Langlands.ProfiniteCohomology.cohomology T.X₂ 3))
                (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
              (Langlands.GaloisCohomology.realLocalization ι T.X₂ (↑w) 3) x) →
            Langlands.GaloisCohomology.globalEulerRatio ι T.X₂ =
              Langlands.GaloisCohomology.globalEulerRatio ι T.X₁ * Langlands.GaloisCohomology.globalEulerRatio ι T.X₃
@Langlands.GaloisCohomology.globalEulerRatio_shortExact : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {T :
    CategoryTheory.ShortComplex (Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))}
  [inst_6 : Langlands.IsSmoothRep T.X₁] [inst_7 : Langlands.IsSmoothRep T.X₂] [inst_8 : Langlands.IsSmoothRep T.X₃],
  T.ShortExact →
    ∀ [Finite ↑T.X₂],
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          ↑(Nat.card ↑T.X₂) ∈ v.asIdeal → v ∈ S) →
        Langlands.GaloisCohomology.globalEulerRatio ι T.X₂ =
          Langlands.GaloisCohomology.globalEulerRatio ι T.X₁ * Langlands.GaloisCohomology.globalEulerRatio ι T.X₃
@Langlands.GaloisCohomology.globalEulerRatio_eq_one_of_primary : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      (∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
          [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
          (∀ (m : ↑M), ℓ • m = 0) → Langlands.GaloisCohomology.globalEulerRatio ι M = 1) →
        ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
          [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M] {r : ℕ},
          (∀ (m : ↑M), ℓ ^ r • m = 0) → Langlands.GaloisCohomology.globalEulerRatio ι M = 1
```

## Outline of the proofs

Cut the long exact sequences of `G_S` and of each `G_{K_w}` (w real) after `H²`: the alternating product of the orders of an exact sequence of finite groups is `1`, so `χ(A)χ(C) = χ(B)·#ker(H³A → H³B)` and similarly at `w`. When `H³(G_S, A) ≅ ∏_w H³(K_w, A)` and `H³(G_S, B) ↪ ∏_w H³(K_w, B)`, the two kernels have the same order, and the factors `(#M)^{#∞}` are multiplicative since `#B = #A·#C`. The dévissage is an induction on the exponent; `coind_res_eq_pow` filters `Ind_H^G Res_H M` by the powers of the augmentation ideal of `F_p[G/H]`, whose graded pieces are copies of `M`.

- `globalEulerRatio_shortExact_of_bijective`: **Multiplicativity of the ratio**, assuming that the localization to the real places in degree three is bijective for `A` and injective for `B`.
- `globalEulerRatio_shortExact`: **Multiplicativity of the ratio** on a short exact sequence of finite smooth `G_S`-modules with the places above the order of the middle term in `S`, by Tate's theorem on the real places in degree three (`realLocalizationDegreeThreeStatement`).
- `globalEulerRatio_eq_one_of_primary`: **Dévissage to modules killed by `ℓ`.** If the ratio is `1` for every finite module killed by the prime `ℓ`, it is `1` for every finite module killed by a power of `ℓ`.

## Declarations

`eulerCharacteristic_mul_eq_mul_card_range_δ`, `eulerCharacteristic_mul_eq_mul_card_ker`, `card_X₂_eq_of_shortExact`, `card_ker_eq_prod_card_ker`, `ratio_mul_eq`, `card_realLocal_mul_eq`, `globalEulerRatio_shortExact_of_bijective`, `globalEulerRatio_shortExact`, `exists_card_eq_pow_of_nsmul`, `mem_of_natCard_mem_of_nsmul`, `globalEulerRatio_eq_one_of_primary`, `IsMultiplicativeOn`, `IsMultiplicativeOn.rec`, `IsMultiplicativeOn.mk`, `IsMultiplicativeOn.iso`, `IsMultiplicativeOn.shortExact`, `apply_subrepresentation_congr`, `IsMultiplicativeOn.rangeStep`, `IsMultiplicativeOn.coind_res_eq_pow`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 507 (multiplicativity of φ(G_S, ·) on short exact sequences, from (8.6.13)); (8.6.13), p. 495; (8.6.10) (ii), p. 489 (the real places in degrees ≥ 3).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GsEulerRatioShortExactOfBijective.lean` lines 1–233, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PowDefs.lean` lines 1–23, `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ApplySubrepresentationCongr.lean` lines 1–210, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkMultl.lean` lines 1–59, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/WorkDevis.lean` lines 1–58. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `eulerChar_mul_eq_mul_card_range_δ` → `eulerCharacteristic_mul_eq_mul_card_range_δ`, `eulerChar_mul_eq_mul_card_ker` → `eulerCharacteristic_mul_eq_mul_card_ker`, `gsReal_card_mul_eq` → `card_realLocal_mul_eq`, `gsRealRes_cohomologyMap` → `realLocalization_coeffMap` (of `Langlands.GaloisCohomology.Global.RealPlaces.VanishingTwo`), `gsEulerRatio_shortExact` → `globalEulerRatio_shortExact_of_bijective`, `gsEulerRatio_shortExact_of_bijective` → `globalEulerRatio_shortExact_of_bijective`, `exists_card_eq_pow` → `exists_card_eq_pow_of_nsmul`, `ratio_shortExact_l` → `globalEulerRatio_shortExact`, `ratioOne_of_killed_l` → `globalEulerRatio_eq_one_of_primary`, `ratioOne_of_killed` → `globalEulerRatio_eq_one_of_primary`.
