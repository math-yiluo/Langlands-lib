# The real places in degrees `≥ 3`

`Langlands/GaloisCohomology/Global/RealPlaces/DegreeThreeProof.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω` and `M` a finite smooth `G_S`-module killed by `n ≠ 0`
with the places above `n` in `S`. Consider the localization `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)`.

* `surjective_realLocalization_of_three_le`: it is surjective for `r ≥ 3`, and
  `injective_realLocalization_of_four_le`: injective for `r ≥ 4`: by the vanishing of `Ĥ_cʳ⁺¹(G_S, M)`
  and of `Ĥ_cʳ(G_S, M)` (`tateCompactSupportVanishingStatement`) and the exact sequence of the
  cohomology with compact support (the finite local terms vanish in degrees `≥ 3`); so it is bijective
  for `r ≥ 4` (`bijective_realLocalization_of_four_le`).
* `injective_realLocalization_three`: it is injective in degree `3`: Poitou–Tate duality gives the
  hypotheses of the abstract nine-term sequence (`PoitouTate.tatePoitouTateHypotheses`), whose
  localization in degree `3` is injective (`TatePoitouTateHypotheses.injective_ptTGlobalToLocal_three`).
* **`realLocalizationDegreeThreeStatement : RealLocalizationDegreeThreeStatement`**: hence the
  bijectivity in degree `3`, and in every degree `r ≥ 3` (`bijective_realLocalization_of_nsmul`,
  and `bijective_realLocalization` for the places above `#M` in `S`), by
  `bijective_realLocalization_of_nsmul_of_degreeThree` and `bijective_realLocalization_of_degreeThree` of
  `Langlands.GaloisCohomology.Global.RealPlaces.HighDegree`;
* `realLocalizationEquiv`: the isomorphism `Hʳ(G_S, M) ≃ ∏_{w real} Hʳ(K_w, M)` for `r ≥ 3`.

This is Tate's theorem on the real places (NSW (8.6.10) (ii), Milne I.4.10 (c)).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.surjective_realLocalization_of_three_le.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), n • m = 0) {r : ℕ} (hr : 3 ≤ r) :
  Function.Surjective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
Langlands.GaloisCohomology.injective_realLocalization_of_four_le.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
  Function.Injective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
Langlands.GaloisCohomology.bijective_realLocalization_of_four_le.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
  Function.Bijective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
Langlands.GaloisCohomology.realLocalizationPi.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (r : ℕ) :
  ↑(Langlands.ProfiniteCohomology.cohomology M r) →+
    (w : { w // w.IsReal }) →
      ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) r)
Langlands.GaloisCohomology.realLocalizationPi_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (r : ℕ) (x : ↑(Langlands.ProfiniteCohomology.cohomology M r)) (w : { w // w.IsReal }) :
  (Langlands.GaloisCohomology.realLocalizationPi ι M r) x w = (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
Langlands.GaloisCohomology.injective_realLocalization_three.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), n • m = 0) :
  Function.Injective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) 3) x
Langlands.GaloisCohomology.realLocalizationDegreeThreeStatement.{u} :
  Langlands.GaloisCohomology.RealLocalizationDegreeThreeStatement
Langlands.GaloisCohomology.bijective_realLocalization_of_nsmul.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) {r : ℕ}
  (hr : 3 ≤ r) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [Langlands.IsSmoothRep M] [Finite ↑M] :
  (∀ (m : ↑M), n • m = 0) → Function.Bijective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
Langlands.GaloisCohomology.bijective_realLocalization.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S)
  {r : ℕ} (hr : 3 ≤ r) : Function.Bijective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
Langlands.GaloisCohomology.realLocalizationEquiv.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S)
  {r : ℕ} (hr : 3 ≤ r) :
  ↑(Langlands.ProfiniteCohomology.cohomology M r) ≃+
    ((w : { w // w.IsReal }) →
      ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) r))
Langlands.GaloisCohomology.realLocalizationEquiv_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S)
  {r : ℕ} (hr : 3 ≤ r) (x : ↑(Langlands.ProfiniteCohomology.cohomology M r)) (w : { w // w.IsReal }) :
  (Langlands.GaloisCohomology.realLocalizationEquiv ι S M hS hr) x w =
    (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
```

## Outline of the proofs

Surjectivity in degree `r` and injectivity in degree `r ≥ 4`: `Ĥ_cʳ⁺¹(G_S, M) = 0` and `Ĥ_cʳ(G_S, M) = 0`
(`tateCompactSupportVanishingStatement`) with `surjective_realLocalization_of_subsingleton` and
`injective_realLocalization_of_subsingleton`. Injectivity in degree `3`: for `n ≠ 1` the hypotheses of
the abstract nine-term sequence hold (`PoitouTate.tatePoitouTateHypotheses`, from the duality at the
finite places, the vanishing and local Tate duality), whose localization in degree `3` is injective
(`TatePoitouTateHypotheses.injective_ptTGlobalToLocal_three`), and the finite local terms vanish
(`subsingleton_cohomology_localModule_of_three_le`); for `n = 1` the group is zero. The degrees `r ≥ 3`
are the Library's `bijective_realLocalization_of_nsmul_of_degreeThree` and `bijective_realLocalization_of_degreeThree` (dimension
shifting along `Ind_{G_S(K(i))}^{G_S}`) applied to `realLocalizationDegreeThreeStatement`.

## Declarations

`surjective_realLocalization_of_three_le`, `injective_realLocalization_of_four_le`, `bijective_realLocalization_of_four_le`, `realLocalizationPi`, `realLocalizationPi_apply`, `injective_realLocalization_three`, `realLocalizationDegreeThreeStatement`, `bijective_realLocalization_of_nsmul`, `bijective_realLocalization`, `realLocalizationEquiv`, `realLocalizationEquiv_apply`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/Vanishing.lean` (lines 39–79: `injective_gsRealRes_of_four_le`, `surjective_gsRealRes_of_three_le`) and `src/GroundTheory/ProfiniteCohomology/PoitouTate/NonemptyOfNatCastMemOfNeOne.lean` (lines 130–150: `injective_gsRealRes_three`, `bijective_gsRealRes`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Stated with the Library's `realLocalization` and `RealLocalizationDegreeThreeStatement`; the injectivity in degree `3` takes the hypotheses of the abstract nine-term sequence from `PoitouTate.tatePoitouTateHypotheses`; `realLocalizationPi` and `realLocalizationEquiv` have no counterpart in the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10) (long exact sequence of Poitou–Tate; (ii): `Hⁱ(G_S, A) ≅ ⊕_{𝔭 real} Hⁱ(k_𝔭, A)` for `i ≥ 3`), statement p. 489, proof of (ii) pp. 490–491 (degree `3` from the duality of the class formation (8.4.4) and (7.2.17); the degrees `i ≥ 3` by the exact sequence `0 → A → Ind A → B → 0` and induction).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 ((c): `Hʳ(G_S, M) ≅ ∏_{v real} Hʳ(K_v, M)` for `r ≥ 3`); proof pp. 60–61 (p. 61: the exact sequence ending in `H³(G_S, M) → ⊕_{v real} H³(G_v, M) → 0` and the isomorphisms for `r ≥ 4`, from the class formation).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VII, §2, (7.2.17), p. 390 (duality for `G(ℂ|ℝ)`; in its proof the Kummer sequence `1 → μ₂ → ℂˣ → ℂˣ → 1` gives `H²(G, ℂˣ) ≅ H³(G, μ₂)`).
