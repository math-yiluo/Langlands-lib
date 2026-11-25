# Statement: the `ℓ`-cohomological dimension of `G_S`

`Langlands/GaloisCohomology/Global/Dimension/Statement.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K` and
`G_S = Gal(K_S/K)` the Galois group of the maximal extension of `K` in `Ω` unramified outside `S`
(ramification at the infinite places allowed). `cd ℓ G` is the `ℓ`-cohomological dimension of the
module `Langlands.Cohomology.Profinite.Dimension.Basic`.

**Statement** (`CohomologicalDimensionStatement`). For every prime `ℓ` such that every finite place
above `ℓ` lies in `S` and `ℓ` is odd or `K` has no real place, `cd_ℓ(G_S) ≤ 2`.

The statement is proved in `Langlands.GaloisCohomology.Global.Dimension.Proof`
(`cohomologicalDimensionStatement`). For `ℓ = 2` and `K` with a real place the dimension is infinite
(NSW (8.3.19) and the remark after it, p. 464), which is why the condition is there.

**Consequences** (in the namespace `CohomologicalDimensionStatement`, from the statement). Let `n ≠ 0`
be such that every finite place above `n` lies in `S`, with `n` odd or `K` totally complex.
1. (`subsingleton_cohomology_res_of_three_le`) For an open subgroup `U` of `G_S` and a smooth module
   `M` of `U` killed by `n`, `Hʳ(U, M) = 0` for every `r ≥ 3`.
2. (`subsingleton_cohomology_of_three_le`) For a smooth module `M` of `G_S` killed by `n`,
   `Hʳ(G_S, M) = 0` for every `r ≥ 3`.

Proof of the consequences. The cohomology of an `n`-torsion module is `n`-torsion; its `ℓ`-primary
part for `ℓ ∣ n` vanishes above `cd_ℓ(U) ≤ cd_ℓ(G_S) ≤ 2` (`primaryComponent_cohomology_eq_bot_of_cd_lt`,
`cd_openSubgroup_le`), as in the local theory (`Langlands.GaloisCohomology.Local.Dimension`,
`subsingleton_cohomology_res_of_three_le`).

## Complete types

```lean
Langlands.GaloisCohomology.CohomologicalDimensionStatement : Prop
Langlands.GaloisCohomology.CohomologicalDimensionStatement.subsingleton_cohomology_res_of_three_le : Langlands.GaloisCohomology.CohomologicalDimensionStatement →
  ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ},
    n ≠ 0 →
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
        Odd n ∨ NumberField.IsTotallyComplex K →
          ∀ (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
            (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) ↥↑U) [inst_5 : Langlands.IsSmoothRep M],
            (∀ (m : ↑M), n • m = 0) → ∀ {r : ℕ}, 3 ≤ r → Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology M r)
Langlands.GaloisCohomology.CohomologicalDimensionStatement.subsingleton_cohomology_of_three_le : Langlands.GaloisCohomology.CohomologicalDimensionStatement →
  ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ},
    n ≠ 0 →
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
        Odd n ∨ NumberField.IsTotallyComplex K →
          ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
            [inst_5 : Langlands.IsSmoothRep M],
            (∀ (m : ↑M), n • m = 0) → ∀ {r : ℕ}, 3 ≤ r → Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology M r)
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §3, (8.3.18)
  Proposition, p. 463 (`cd_p G_S ≤ 2` for `S_p ∪ S_∞ ⊆ S`, `k` totally imaginary if `p = 2`); (8.3.19)
  Proposition and the remark after it, p. 464.

## Source and licence

The statement is written for the Library. The consequences follow the pattern of
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/Dimension.lean` (lines 113–137,
`cdp_galUnramifiedOutside_le_two_of_dvd`, `subsingleton_cohomology_gs_of_three_le`) of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`, and the Library's local file `Langlands.GaloisCohomology.Local.Dimension`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).
