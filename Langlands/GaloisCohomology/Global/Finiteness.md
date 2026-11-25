# Finiteness of the cohomology of `G_S`

`Langlands/GaloisCohomology/Global/Finiteness.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)` the Galois group of the maximal extension of `K` in `Ω` unramified outside `S`
(ramification at the infinite places allowed), `𝒪_Sˣ` the `S`-units of `K_S` and `μ_ℓ` the `ℓ`-th
roots of unity in `K_S`.

**Theorem.**
1. (`finite_nsmul_eq_zero_cohomology_two_maximalSUnits`) For a prime `ℓ` with the places above `ℓ`
   in `S`, the `ℓ`-torsion of `H²(G_S, 𝒪_Sˣ)` is finite.
2. (`finite_cohomology_one_rootsOfUnityModule`, `finite_cohomology_two_rootsOfUnityModule`)
   `H¹(G_S, μ_ℓ)` and `H²(G_S, μ_ℓ)` are finite; (`finite_cohomology_res_rootsOfUnityModule`) so is
   `Hʳ(U, μ_ℓ)` for `r ≤ 2` and every open subgroup `U` of `G_S`.
3. (`finite_cohomology_res_of_le_two`) For `n ≠ 0` with the places above `n` in `S`, an open subgroup
   `U` of `G_S` and a finite smooth module `M` of `U` killed by `n`, `Hʳ(U, M)` is finite for `r ≤ 2`;
   (`finite_cohomology_of_le_two`) the same for `G_S` and a finite smooth module `M` with the places
   above `#M` in `S`.
4. (`finite_cohomology_of_odd_or_isTotallyComplex`) If moreover `#M` is odd or `K` is totally complex,
   `Hʳ(G_S, M)` is finite for every `r`.

This is NSW (8.3.20) (i) in degrees `≤ 2`, and in all degrees when `#M` is odd or `K` totally
complex; with real places and `#M` even, the degrees `≥ 3` are the cohomology of the real places
(NSW (8.6.10) (ii), p. 489), which this file does not treat.

Proof. (1) An `ℓ`-torsion class is determined by its image in the Brauer group of `K`
(`eq_zero_of_maximalSUnitsInflation_eq_zero`), which vanishes outside `S`
(`brauerLocalization_maximalSUnitsInflation_eq_zero`) and is determined by its localizations
(`eq_zero_of_brauerLocalization_eq_zero'`); the `ℓ`-torsion of each local Brauer group is finite
(`finite_nsmul_eq_zero_localBrauerGroup`, `finite_nsmul_eq_zero_realBrauerGroup`, through the
invariants in `ℚ/ℤ`, `finite_nsmul_eq_zero_rationalModIntegers`). (2) The Kummer sequence
`0 → μ_ℓ → 𝒪_Sˣ → 𝒪_Sˣ → 0` (`sUnitsKummerSequence_shortExact`): `H¹(G_S, μ_ℓ)` maps to `Pic(𝒪_S)`,
which is finite (`finite_sPicardGroup`), with kernel the image of the Kummer map of the `S`-units of
`K` (`kummerPicHom_eq_zero_iff`), a finitely generated group (the `S`-unit theorem,
`Langlands.Global.Arithmetic.SUnitIndex`) killed by `ℓ`, hence finite; `H²(G_S, μ_ℓ)` sits between
`H¹(G_S, 𝒪_Sˣ)`, which embeds into `Pic(𝒪_S)` (`cohomologyOneSUnitsToSPicard_injective`), and the
`ℓ`-torsion of `H²(G_S, 𝒪_Sˣ)`, finite by (1). An open subgroup of `G_S` is `G_{S_L}` of a finite
extension `L ⊆ K_S` with `S_L` finite (`fixingOpenSubgroupEquiv`, `finite_finitePlacesAbove`). (3) The
dévissage of the local theory (`finite_cohomology_of_forall_trivial`) reduces to trivial modules over
an open subgroup fixing `μ_n` (`rootsOfUnityFixing` of `Langlands.GaloisCohomology.Local.Finiteness`);
these are filtered with quotients
`ℤ/ℓ ≅ μ_ℓ` (`finite_cohomology_of_trivial_maximal`, by induction on the order, as the local
`finite_cohomology_of_trivial`). (4) Above degree two the groups vanish
(`CohomologicalDimensionStatement.subsingleton_cohomology_of_three_le`).

Declarations, in order: `exists_fin_eq_rationalClass_of_nsmul_eq_zero`,
`finite_nsmul_eq_zero_rationalModIntegers`, `finite_nsmul_eq_zero_localBrauerGroup`,
`finite_nsmul_eq_zero_realBrauerGroup`, `finite_nsmul_eq_zero_cohomology_two_maximalSUnits`,
`finite_cohomology_one_rootsOfUnityModule`, `finite_cohomology_two_rootsOfUnityModule`,
`finite_cohomology_res_rootsOfUnityModule`, `finite_cohomology_of_trivial_maximal`,
`finite_cohomology_res_of_le_two`, `finite_cohomology_of_le_two`,
`finite_cohomology_of_odd_or_isTotallyComplex`.

## Complete types

```lean
@Langlands.GaloisCohomology.exists_fin_eq_rationalClass_of_nsmul_eq_zero : ∀ {m : ℕ},
  m ≠ 0 →
    ∀ {q : Langlands.ClassFieldTheory.Local.RationalModIntegers},
      m • q = 0 → ∃ (k : Fin m), q = Langlands.ClassFieldTheory.Local.rationalClass (↑↑k / ↑m)
@Langlands.GaloisCohomology.finite_nsmul_eq_zero_rationalModIntegers : ∀ {m : ℕ},
  m ≠ 0 → Finite { q : Langlands.ClassFieldTheory.Local.RationalModIntegers // m • q = 0 }
@Langlands.GaloisCohomology.finite_nsmul_eq_zero_localBrauerGroup : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {m : ℕ},
  m ≠ 0 → Finite { a : Langlands.GaloisCohomology.LocalBrauerGroup v // m • a = 0 }
@Langlands.GaloisCohomology.finite_nsmul_eq_zero_realBrauerGroup : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K) {m : ℕ},
  m ≠ 0 → Finite { b : Langlands.GaloisCohomology.RealBrauerGroup w // m • b = 0 }
@Langlands.GaloisCohomology.finite_nsmul_eq_zero_cohomology_two_maximalSUnits : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ [Finite ↑S],
        Finite
          { y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2) //
            ℓ • y = 0 }
@Langlands.GaloisCohomology.finite_cohomology_one_rootsOfUnityModule : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ [Finite ↑S],
        Finite
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) ℓ)
              1)
@Langlands.GaloisCohomology.finite_cohomology_two_rootsOfUnityModule : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ [Finite ↑S],
        Finite
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) ℓ)
              2)
@Langlands.GaloisCohomology.finite_cohomology_res_rootsOfUnityModule : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ [Finite ↑S] (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)),
        ∀ r ≤ 2,
          Finite
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Rep.res (↑U).subtype
                  (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
                    ℓ))
                r)
@Langlands.GaloisCohomology.finite_cohomology_of_trivial_maximal : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S] {n : ℕ},
  n ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
      ∀ (V : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)),
        (∀ σ ∈ V, ∀ (ζ : ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)), ζ ^ n = 1 → σ ζ = ζ) →
          ∀ (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) ↥↑V) [inst_6 : Langlands.IsSmoothRep A] [Finite ↑A],
            (∀ (g : ↥↑V) (a : ↑A), (A.ρ g) a = a) →
              (∀ (a : ↑A), n • a = 0) → ∀ r ≤ 2, Finite ↑(Langlands.ProfiniteCohomology.cohomology A r)
@Langlands.GaloisCohomology.finite_cohomology_res_of_le_two : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S] {n : ℕ},
  n ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
      ∀ (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
        (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) ↥↑U) [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
        (∀ (m : ↑M), n • m = 0) → ∀ r ≤ 2, Finite ↑(Langlands.ProfiniteCohomology.cohomology M r)
@Langlands.GaloisCohomology.finite_cohomology_of_le_two : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S) →
    ∀ r ≤ 2, Finite ↑(Langlands.ProfiniteCohomology.cohomology M r)
@Langlands.GaloisCohomology.finite_cohomology_of_odd_or_isTotallyComplex : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S) →
    Odd (Nat.card ↑M) ∨ NumberField.IsTotallyComplex K →
      ∀ (r : ℕ), Finite ↑(Langlands.ProfiniteCohomology.cohomology M r)
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §3, (8.3.20)
  Theorem (i) and its proof, pp. 464–465; (8.3.11) Proposition, p. 458.
- For the degrees above two with real places: NSW, Chapter VIII §6, (8.6.10) (ii), p. 489.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files under
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`: `Finite.lean` (lines 99–224, the
reduction to roots of unity over an open subgroup) and `FiniteRoots.lean` (lines 24–171, the Kummer
argument for `μ_n`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the dévissage
and the induction on the order are the Library's local ones (`Langlands.GaloisCohomology.Local.Finiteness`)
for `G_S`; the finiteness of the `S`-units modulo `ℓ` uses the Library's `S`-unit theorem; the
`ℓ`-torsion of `H²(G_S, 𝒪_Sˣ)` is bounded through the Library's Brauer sequence.
