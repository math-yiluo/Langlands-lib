# Proof: the `ℓ`-cohomological dimension of `G_S`

`Langlands/GaloisCohomology/Global/Dimension/Proof.lean`, namespace `Langlands.GaloisCohomology`.

Notation as in `Langlands.GaloisCohomology.Global.Dimension.Statement`; `μ_ℓ` is
`rootsOfUnityModule K K_S ℓ`, `𝒪_Sˣ` the `S`-units of `K_S`, and `ℓ` a prime such that every finite
place above `ℓ` lies in `S`, with `ℓ` odd or `K` totally complex.

**Theorem.**
1. (`subsingleton_cohomology_three_rootsOfUnityModule`) `H³(G_S, μ_ℓ) = 0`.
2. (`subsingleton_cohomology_three_res_rootsOfUnityModule`) `H³(U, μ_ℓ) = 0` for every open subgroup
   `U` of `G_S`.
3. (`cd_galoisGroupUnramifiedOutside_le_two`) `cd_ℓ(G_S) ≤ 2`; `cohomologicalDimensionStatement`
   proves `CohomologicalDimensionStatement`.
4. (`eq_zero_of_cohomology_maximalSUnits_of_three_le`) `Hʳ(G_S, 𝒪_Sˣ)(ℓ) = 0` for every `r ≥ 3`.

This is NSW (8.3.18), with the proof given there.

Proof. (1) `μ_ℓ ⊆ K_S` and `0 → μ_ℓ → 𝒪_Sˣ → 𝒪_Sˣ → 0` (multiplication by `ℓ`) is exact
(`sUnitsKummerSequence_shortExact`). The connecting map `H²(G_S, 𝒪_Sˣ) → H³(G_S, μ_ℓ)` vanishes
because `H²(G_S, 𝒪_Sˣ)` is `ℓ`-divisible (`exists_prime_nsmul_eq_cohomology_two_maximalSUnits`), so
`H³(G_S, μ_ℓ) → H³(G_S, 𝒪_Sˣ)` is injective; its image is killed by `ℓ`
(`nsmul_rootsOfUnityModule_eq_zero`) and `H³(G_S, 𝒪_Sˣ)(ℓ) = 0`
(`eq_zero_of_cohomology_three_maximalSUnits`). (2) `U` fixes a finite extension `L ⊆ K_S` of `K` and
is `G_{S_L}` of `L` for the places `S_L` above `S` (`exists_fixingOpenSubgroup_eq`,
`fixingOpenSubgroupEquiv`); `μ_ℓ(K_S)` is `μ_ℓ` of the maximal extension of `L` unramified outside
`S_L` (`MulEquiv.restrictRootsOfUnity`), so (1) for `L` applies (`isIso_map_of_mulEquiv`). (3) A
pro-`ℓ` Sylow subgroup `P` of `G_S` has the same `cd_ℓ` (`cd_eq_of_isProSylow`), and
`cd_ℓ(P) ≤ 2` iff `H³(P, ℤ/ℓ) = 0` (`cd_le_iff_of_isProPGroup`). `P` fixes `μ_ℓ`
(`apply_eq_of_isProPGroup` of `Langlands.GaloisCohomology.Local.Dimension`, for the integral
extension `K_S/K`: the action on `μ_ℓ` factors through `(ℤ/ℓ)ˣ`), so
`μ_ℓ ≅ ℤ/ℓ` over `P` (`nonempty_zmod_addEquiv_rootsOfUnity_maximal`), and `H³(P, μ_ℓ)` is the limit of
the groups `H³(U, μ_ℓ)` over the open subgroups `U ⊇ P` (`exists_resOfLE_eq`), which vanish by (2).
(4) Multiplication by `ℓ` on `Hʳ(G_S, 𝒪_Sˣ)` is injective since `Hʳ(G_S, μ_ℓ) = 0` for `r ≥ 3`
(`CohomologicalDimensionStatement.subsingleton_cohomology_of_three_le`).

Declarations, in order: `nsmul_rootsOfUnityModule_eq_zero`, `nonempty_zmod_addEquiv_rootsOfUnity_maximal`,
`subsingleton_cohomology_three_rootsOfUnityModule`,
`subsingleton_cohomology_three_res_rootsOfUnityModule`, `cd_galoisGroupUnramifiedOutside_le_two`,
`cohomologicalDimensionStatement`, `eq_zero_of_cohomology_maximalSUnits_of_three_le`.

## Complete types

```lean
@Langlands.GaloisCohomology.nsmul_rootsOfUnityModule_eq_zero : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (n : ℕ) (a : ↑(Langlands.GaloisCohomology.rootsOfUnityModule F E n)), n • a = 0
@Langlands.GaloisCohomology.nonempty_zmod_addEquiv_rootsOfUnity_maximal : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      Nonempty (ZMod ℓ ≃+ Additive ↥(rootsOfUnity ℓ ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)))
@Langlands.GaloisCohomology.subsingleton_cohomology_three_rootsOfUnityModule : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ℓ ≠ 2 ∨ NumberField.IsTotallyComplex K →
        Subsingleton
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) ℓ)
              3)
@Langlands.GaloisCohomology.subsingleton_cohomology_three_res_rootsOfUnityModule : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ℓ ≠ 2 ∨ NumberField.IsTotallyComplex K →
        ∀ (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)),
          Subsingleton
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Rep.res (↑U).subtype
                  (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
                    ℓ))
                3)
@Langlands.GaloisCohomology.cd_galoisGroupUnramifiedOutside_le_two : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ℓ ≠ 2 ∨ NumberField.IsTotallyComplex K →
        Langlands.ProfiniteCohomology.cd ℓ (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) ≤ 2
Langlands.GaloisCohomology.cohomologicalDimensionStatement : Langlands.GaloisCohomology.CohomologicalDimensionStatement
@Langlands.GaloisCohomology.eq_zero_of_cohomology_maximalSUnits_of_three_le : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ℓ ≠ 2 ∨ NumberField.IsTotallyComplex K →
        ∀ {r : ℕ},
          3 ≤ r →
            ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) r))
              {k : ℕ}, ℓ ^ k • x = 0 → x = 0
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §3, (8.3.18)
  Proposition and its proof, p. 463; (8.3.11) Proposition (iv), p. 458.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files under
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`: `Dimension.lean` (lines 41–110:
`nonempty_zmod_addEquiv_rootsOfUnity_gs`, `subsingleton_h3_rootsOfUnity`,
`subsingleton_h3_res_rootsOfUnity`, `cdp_galUnramifiedOutside_le_two`, here
`nonempty_zmod_addEquiv_rootsOfUnity_maximal`, `subsingleton_cohomology_three_rootsOfUnityModule`,
`subsingleton_cohomology_three_res_rootsOfUnityModule`, `cd_galoisGroupUnramifiedOutside_le_two`) and
`DimensionKummer.lean` (lines 14–67, the Kummer argument). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the Kummer
sequence of `S`-units, the transport to open subgroups and the Sylow argument use the Library's
`sUnitsKummerSequence_shortExact`, `fixingOpenSubgroupEquiv` and the local proof of `cd_le_two`; the
corollary on `Hʳ(G_S, 𝒪_Sˣ)` is new.
