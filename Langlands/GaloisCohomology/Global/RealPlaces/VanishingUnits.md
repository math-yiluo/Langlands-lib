# `H³(G_S, μ₂)` and the real places, through the `S`-units

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingUnits.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K` containing the places
above `2`, `G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω` and `μ₂ = μ₂(K_S)` (`dualizingModule K Ω S 2`).

**Theorem** (`bijective_realLocalization_dualizingModule_two`). The localization
`H³(G_S, μ₂) → ∏_{w real} H³(K_w, μ₂)` is bijective.

On the way:

* with `realKummerSequence ι S N w` of the module `Langlands.GaloisCohomology.Global.PoitouTate.EvenDuality`
  (the Kummer sequence `0 → μ_N(K_S) → K̄_wˣ → K̄_wˣ → 0` at an infinite place, short exact when `N` is
  invertible outside `S`, `realKummerSequence_shortExact`): `sUnitsRealHom`, the
  map `𝒪_Sˣ → K̄_wˣ` of `ι`, and `kummerRealMap`, the morphism from the restriction of the Kummer sequence
  of the `S`-units to it; `realLocalization_δ_kummer`: the connecting maps commute with the localization.
* `map_sUnitsRealHom_eq`: the localization of `Hⁿ(G_S, 𝒪_Sˣ)` at `w` is the localization at `w` of its
  image in `Hⁿ(Gal(Ω/K), Ωˣ)`.
* `subsingleton_cohomology_three_unitsModule_of_isReal`: `H³(K_w, K̄_wˣ) = 0` at a real place;
  `bijective_δ_realKummerSequence_two`: `H²(K_w, K̄_wˣ) → H³(K_w, μ₂)` is bijective.
* `realTrivialSUnitsClasses`, `exists_two_nsmul_eq_of_realBrauerLocalization_eq_zero`: the classes of
  `H²(G_S, 𝒪_Sˣ)` whose image in the Brauer group of `K` vanishes at the infinite places form a
  `2`-divisible group.
* `exists_δ_kummer_eq`: every class of `H³(G_S, μ₂)` is the connecting image of a class of
  `H²(G_S, 𝒪_Sˣ)`; `realLocalization_δ_kummer_eq`, `δ_kummer_eq_zero`,
  `exists_realBrauerLocalization_maximalSUnitsInflation_eq`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.sUnitsRealHom.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (w : NumberField.InfinitePlace K) :
  Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) w ⟶
    Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)
Langlands.GaloisCohomology.sUnitsRealHom_hom_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (w : NumberField.InfinitePlace K)
  (x : Additive ↥(Langlands.GaloisCohomology.maximalSUnits K Ω S)) :
  ↑(Additive.toMul ((Rep.Hom.hom (Langlands.GaloisCohomology.sUnitsRealHom ι S w)) x)) =
    (ι.infinite w) ↑↑↑(Additive.toMul x)
Langlands.GaloisCohomology.kummerRealMap.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (w : NumberField.InfinitePlace K) :
  (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) N).map
      (Rep.resFunctor ↑(Langlands.Galois.realLocalizationHom ι S w)) ⟶
    Langlands.GaloisCohomology.realKummerSequence ι S N w
Langlands.GaloisCohomology.realLocalization_δ_kummer.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {N : ℕ} [NeZero N]
  (hNS : ∀ v ∉ S, ↑N ∉ v.asIdeal)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (w : NumberField.InfinitePlace K) (r : ℕ)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) r)) :
  have this := ⋯;
  (Langlands.GaloisCohomology.realLocalization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) w
        (r + 1))
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ r (r + 1) ⋯)) y) =
    (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ r (r + 1) ⋯))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (Langlands.Galois.realLocalizationHom ι S w)
            (Langlands.GaloisCohomology.sUnitsRealHom ι S w) r))
        y)
Langlands.GaloisCohomology.map_sUnitsRealHom_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (w : NumberField.InfinitePlace K)
  (n : ℕ) (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) n)) :
  (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (Langlands.Galois.realLocalizationHom ι S w)
          (Langlands.GaloisCohomology.sUnitsRealHom ι S w) n))
      y =
    (Langlands.GaloisCohomology.realBrauerLocalization ι w n)
      ((Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S n) y)
Langlands.GaloisCohomology.subsingleton_cohomology_three_unitsModule_of_isReal.{u} {K : Type u} [Field K]
  [NumberField K] (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
  Subsingleton
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 3)
Langlands.GaloisCohomology.bijective_δ_realKummerSequence_two.{u} {K : Type u} [Field K] [NumberField K] {Ω : Type u}
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
  Function.Bijective ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 2 3 ⋯))
Langlands.GaloisCohomology.realTrivialSUnitsClasses.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  AddSubgroup ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)
Langlands.GaloisCohomology.mem_realTrivialSUnitsClasses_iff.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)) :
  y ∈ Langlands.GaloisCohomology.realTrivialSUnitsClasses ι S ↔
    ∀ (w : NumberField.InfinitePlace K),
      (Langlands.GaloisCohomology.realBrauerLocalization ι w 2)
          ((Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) y) =
        0
Langlands.GaloisCohomology.exists_two_nsmul_eq_of_realBrauerLocalization_eq_zero.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  (y : ↥(Langlands.GaloisCohomology.realTrivialSUnitsClasses ι S)) : ∃ y', 2 • y' = y
Langlands.GaloisCohomology.exists_δ_kummer_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  (hK :
    (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
        2).ShortExact)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S 2) 3)) :
  ∃ y, (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ hK 2 3 ⋯)) y = x
Langlands.GaloisCohomology.realLocalization_δ_kummer_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  (hK :
    (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
        2).ShortExact)
  (w : NumberField.InfinitePlace K)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)) :
  (Langlands.GaloisCohomology.realLocalization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S 2) w 3)
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ hK 2 3 ⋯)) y) =
    (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 2 3 ⋯))
      ((Langlands.GaloisCohomology.realBrauerLocalization ι w 2)
        ((Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) y))
Langlands.GaloisCohomology.δ_kummer_eq_zero.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  (hK :
    (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
        2).ShortExact)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
  (hy :
    ∀ (w : NumberField.InfinitePlace K),
      w.IsReal →
        (Langlands.GaloisCohomology.realLocalization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S 2) w
              3)
            ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ hK 2 3 ⋯)) y) =
          0) :
  (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ hK 2 3 ⋯)) y = 0
Langlands.GaloisCohomology.exists_realBrauerLocalization_maximalSUnitsInflation_eq.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S)
  (b : (w : { w // w.IsReal }) → Langlands.GaloisCohomology.RealBrauerGroup ↑w) :
  ∃ y,
    ∀ (w : { w // w.IsReal }),
      (Langlands.GaloisCohomology.realBrauerLocalization ι (↑w) 2)
          ((Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) y) =
        b w
Langlands.GaloisCohomology.bijective_realLocalization_dualizingModule_two.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S) :
  Function.Bijective fun x w =>
    (Langlands.GaloisCohomology.realLocalization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S 2) (↑w)
        3)
      x
```

## Outline of the proofs

The Kummer sequence of the `S`-units (`sUnitsKummerSequence_shortExact`) gives
`H²(G_S, 𝒪_Sˣ) → H³(G_S, μ₂) → H³(G_S, 𝒪_Sˣ)[2]`, and `H³(G_S, 𝒪_Sˣ)(2) = 0`
(`eq_zero_of_cohomology_three_maximalSUnits`). At a real place the Galois group has order `2`: its
cohomology is periodic (`isZero_groupCohomology_odd`, through `isoGroupCohomology`), so Hilbert 90
(`isZero_cohomology_one_unitsModule`) gives `H³(K_w, K̄_wˣ) = 0`, and `H²(K_w, K̄_wˣ)` is killed by `2`
(`two_nsmul_cohomology_closureGalois`); hence the connecting map of the real Kummer sequence is bijective.
The connecting maps commute with the localization (`δ_comp_map`), and the localization of a class of
`H²(G_S, 𝒪_Sˣ)` is read in the Brauer group of `K` (`maximalSUnitsInflation`, `realBrauerLocalization`).
Surjectivity: prescribed real local classes, with a class at one place of `S` making the sum of the
invariants zero, come from a `2`-primary class (`existsUnique_maximalSUnitsInflation_localization`).
Injectivity: a class with trivial real localizations is divisible by `2`
(`exists_prime_nsmul_eq_of_primary`; for a `2`-primary class the local invariants are halved keeping their
sum zero, `exists_rationalModIntegers_nsmul_eq`, `exists_localInvariant_eq`,
`exists_maximalSUnitsInflation_eq`, as in `exists_prime_nsmul_eq_cohomology_two_maximalSUnits`), and
`H³(G_S, μ₂)` is killed by `2`.

## Declarations

`sUnitsRealHom`, `sUnitsRealHom_hom_apply`, `kummerRealMap`, `realLocalization_δ_kummer`, `map_sUnitsRealHom_eq`, `subsingleton_cohomology_three_unitsModule_of_isReal`, `bijective_δ_realKummerSequence_two`, `realTrivialSUnitsClasses`, `mem_realTrivialSUnitsClasses_iff`, `exists_two_nsmul_eq_of_realBrauerLocalization_eq_zero`, `exists_δ_kummer_eq`, `realLocalization_δ_kummer_eq`, `δ_kummer_eq_zero`, `exists_realBrauerLocalization_maximalSUnitsInflation_eq`, `bijective_realLocalization_dualizingModule_two`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VII, §2, (7.2.17), p. 390 (duality for `G(ℂ|ℝ)`; in its proof the Kummer sequence `1 → μ₂ → ℂˣ → ℂˣ → 1` gives `H²(G, ℂˣ) ≅ H³(G, μ₂)`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §3, (8.3.11), p. 458 (the Brauer group of `K` and `H²(G_S, 𝒪_Sˣ)`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10) (long exact sequence of Poitou–Tate; (ii): `Hⁱ(G_S, A) ≅ ⊕_{𝔭 real} Hⁱ(k_𝔭, A)` for `i ≥ 3`), statement p. 489, proof of (ii) pp. 490–491 (degree `3` from the duality of the class formation (8.4.4) and (7.2.17); the degrees `i ≥ 3` by the exact sequence `0 → A → Ind A → B → 0` and induction).
