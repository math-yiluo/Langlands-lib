# `H²` of the `S`-units and the Brauer group outside `S`

`Langlands/GaloisCohomology/Global/Units/Brauer.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K`, `K_S` the
maximal extension unramified outside `S` (ramification at the infinite places allowed),
`G_S = Gal(K_S/K)`, `𝒪_Sˣ` the `S`-units of `K_S`, `ι : PlaceEmbeddings K Ω`, and `ℓ` a prime such that
`S` contains the places above `ℓ`. `maximalSUnitsInflation K Ω S n : Hⁿ(G_S, 𝒪_Sˣ) → Hⁿ(Gal(Ω/K), Ωˣ)`
is the map through `K_Sˣ`.

**Theorem.**
1. (`eq_zero_of_maximalSUnitsInflation_eq_zero`) In degree `2` it is injective on classes killed by a
   power of `ℓ`.
2. (`brauerLocalization_maximalSUnitsInflation_eq_zero`) Its image vanishes at every finite place
   outside `S` (for every `S`, with no condition on `ℓ`).
3. (`exists_maximalSUnitsInflation_eq`) Every Brauer class of `K` killed by a power of `ℓ` and
   vanishing at the finite places outside `S` is the image of a class killed by a power of `ℓ`.
4. (`maximalSUnitsPrimaryEquiv`) Hence `H²(G_S, 𝒪_Sˣ)(ℓ)` is isomorphic to the group
   `brauerPrimaryOutside S ι ℓ` of `ℓ`-primary Brauer classes vanishing outside `S`, and
   (`existsUnique_maximalSUnitsInflation_localization`) its elements correspond to the families of
   `ℓ`-primary local classes at the places of `S` and the real places with sum of invariants zero.
5. (`exists_prime_nsmul_eq_cohomology_two_maximalSUnits`) If `ℓ ≠ 2` or `K` has no real place,
   `H²(G_S, 𝒪_Sˣ)` is `ℓ`-divisible.

This is NSW (8.3.11) (iii) and (8.3.12) (i), with a different proof: NSW use the class formation of
`S`-idèle classes, here the divisors of `K_S` prime to `S` are used instead, as in the source.

Proof. (1) `maximalUnitsInflation` is injective in degree `2`, so the class is the image of
`H¹(G_S, K_Sˣ/𝒪_Sˣ)`, which is killed by integers prime to `ℓ`
(`Langlands.GaloisCohomology.Global.Units.DivisorSequence`). (2) The divisor of an `S`-unit is zero,
and the local class at `v ∉ S` vanishes with the order class (`brauerLocalization_maximalUnitsInflation_eq_zero_iff`).
(3) The class dies in a totally complex subextension of `K_S` with large local degrees
(`Langlands.GaloisCohomology.Global.Units.ComplexRestriction`), so it is inflated from some
`z ∈ H²(G_S, K_Sˣ)` (`exists_maximalUnitsInflation_eq`); the components of the divisor class of `z`
vanish, so the divisor class vanishes (`eq_zero_of_divisorEval_eq_zero`); the image of `z` in
`H²(G_S, K_Sˣ/𝒪_Sˣ)` lies in the kernel to `H²(G_S, D)`, which is killed by integers prime to `ℓ`, and is
`ℓ`-primary, hence zero; so `z` comes from `H²(G_S, 𝒪_Sˣ)`, and an `ℓ`-primary preimage is taken
(`exists_primary_map_eq`). (4) From (1)–(3) and the Library's `existsUnique_brauerLocalization_eq'`,
`eq_zero_of_brauerLocalization_eq_zero'`. (5) The part prime to `ℓ` is divisible
(`exists_prime_nsmul_eq_of_primary`); for an `ℓ`-primary class the real components of its image
vanish (`eq_zero_realBrauerGroup_of_odd`, or no real places), its local invariants are divided by
`ℓ` keeping the sum zero (`exists_rationalModIntegers_nsmul_eq`, the correction at a place of `S`
where the class is nonzero), the global class with these invariants exists (the Library's
`exists_localInvariant_eq`) and lifts by (3); injectivity (1) concludes.

The restriction to `ℓ`-primary parts in capitulation is removed in the module
`Langlands.GaloisCohomology.Global.Units.CapitulationPrincipalIdeal`, which imports the bridge
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal` to the principal ideal theorem of the NYLL copy:
for every finite level `L` of `K_S / K` there is a finite level `L' ⊇ L` in which every divisor of `L` prime
to `S` is the divisor of a unit (`exists_level_forall_unitsToSDivisor_eq`), so that, for every set `S` of
finite places and with no prime `ℓ`, the divisor map `K_Sˣ → Div_S(K_S)` is onto (`unitsToSDivisor_surjective`)
and the divisor class module is zero (`isZero_sDivisorClassModule`); `0 → 𝒪_Sˣ → K_Sˣ → D → 0` is then short
exact (`sUnitsDivisorSequence_shortExact`) and `K_Sˣ/𝒪_Sˣ → D` is an isomorphism
(`isIso_unitsModSUnitsToSDivisor`). This file does not import the copy; it uses the capitulation through
`exists_coprime_nsmul_cohomology_one_unitsModSUnits`, with integers prime to `ℓ`; its hypothesis that `S`
contains the places above `ℓ` serves also to make `ℓ`-primary Brauer classes die in `K_S`.

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.exists_mul_add_mul_eq_one : ∀ {a b : ℕ},
  a.Coprime b → ∃ (s : ℤ) (t : ℤ), ↑a * s + ↑b * t = 1
@Langlands.GaloisCohomology.exists_prime_nsmul_eq_of_primary : ∀ {G : Type u_1} [inst : AddCommGroup G] {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (y : G), IsOfFinAddOrder y) →
      (∀ (y : G), (∃ (k : ℕ), ℓ ^ k • y = 0) → ∃ (y' : G), ℓ • y' = y) → ∀ (y : G), ∃ (y' : G), ℓ • y' = y
@Langlands.GaloisCohomology.exists_rationalModIntegers_nsmul_eq : ∀ {ℓ : ℕ},
  ℓ ≠ 0 →
    ∀ {k : ℕ} (r : Langlands.ClassFieldTheory.Local.RationalModIntegers),
      ℓ ^ k • r = 0 →
        ∃ (r' : Langlands.ClassFieldTheory.Local.RationalModIntegers),
          ℓ • r' = r ∧ ℓ ^ (k + 1) • r' = 0 ∧ (r = 0 → r' = 0)
@Langlands.GaloisCohomology.two_nsmul_realBrauerGroup : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K) (b : Langlands.GaloisCohomology.RealBrauerGroup w), 2 • b = 0
@Langlands.GaloisCohomology.eq_zero_realBrauerGroup_of_odd : ∀ {K : Type u_1} [inst : Field K] [NumberField K] {ℓ : ℕ},
  Nat.Prime ℓ →
    ℓ ≠ 2 →
      ∀ (w : NumberField.InfinitePlace K) (b : Langlands.GaloisCohomology.RealBrauerGroup w) {k : ℕ},
        ℓ ^ k • b = 0 → b = 0
Langlands.GaloisCohomology.maximalSUnitsInflation : (K Ω : Type u_1) →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (n : ℕ) →
                ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) n) →+
                  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) n)
@Langlands.GaloisCohomology.maximalSUnitsInflation_apply : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) n)),
  (Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S n) y =
    (Langlands.GaloisCohomology.maximalUnitsInflation K Ω S n)
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap
            (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n))
        y)
@Langlands.GaloisCohomology.sUnitsToUnits_comp_unitsToSDivisor : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
      (Langlands.GaloisCohomology.unitsToSDivisor S ι) =
    0
@Langlands.GaloisCohomology.mkQ_comp_unitsModSUnitsToSDivisor : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.sUnitsQuotSequence K Ω S).g
      (Langlands.GaloisCohomology.unitsModSUnitsToSDivisor S ι) =
    Langlands.GaloisCohomology.unitsToSDivisor S ι
@Langlands.GaloisCohomology.brauerLocalization_maximalSUnitsInflation_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)),
      (Langlands.GaloisCohomology.brauerLocalization ι v 2)
          ((Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) y) =
        0
@Langlands.GaloisCohomology.eq_zero_of_maximalSUnitsInflation_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
        {k : ℕ}, ℓ ^ k • y = 0 → (Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) y = 0 → y = 0
@Langlands.GaloisCohomology.exists_maximalSUnitsInflation_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω)
        (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)) {k : ℕ},
        ℓ ^ k • x = 0 →
          (∀ v ∉ S, (Langlands.GaloisCohomology.brauerLocalization ι v 2) x = 0) →
            ∃ (y :
              ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)),
              (∃ (j : ℕ), ℓ ^ j • y = 0) ∧ (Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) y = x
@Langlands.GaloisCohomology.brauerPrimaryOutside : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                ℕ →
                  AddSubgroup ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)
@Langlands.GaloisCohomology.mem_brauerPrimaryOutside : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ℓ : ℕ)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
  x ∈ Langlands.GaloisCohomology.brauerPrimaryOutside S ι ℓ ↔
    (∃ (k : ℕ), ℓ ^ k • x = 0) ∧ ∀ v ∉ S, (Langlands.GaloisCohomology.brauerLocalization ι v 2) x = 0
@Langlands.GaloisCohomology.maximalSUnitsInflationPrimary : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                (ℓ : ℕ) →
                  ↥(AddCommGroup.primaryComponent
                        (↑(Langlands.ProfiniteCohomology.cohomology
                            (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
                        ℓ) →+
                    ↥(Langlands.GaloisCohomology.brauerPrimaryOutside S ι ℓ)
@Langlands.GaloisCohomology.bijective_maximalSUnitsInflationPrimary : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω),
        Function.Bijective ⇑(Langlands.GaloisCohomology.maximalSUnitsInflationPrimary S ι ℓ)
@Langlands.GaloisCohomology.maximalSUnitsPrimaryEquiv : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              {ℓ : ℕ} →
                Nat.Prime ℓ →
                  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
                    (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                      ↥(AddCommGroup.primaryComponent
                            (↑(Langlands.ProfiniteCohomology.cohomology
                                (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
                            ℓ) ≃+
                        ↥(Langlands.GaloisCohomology.brauerPrimaryOutside S ι ℓ)
@Langlands.GaloisCohomology.coe_maximalSUnitsPrimaryEquiv_apply : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (y :
    ↥(AddCommGroup.primaryComponent
        (↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)) ℓ)),
  ↑((Langlands.GaloisCohomology.maximalSUnitsPrimaryEquiv S hℓ hS ι) y) =
    (Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) ↑y
@Langlands.GaloisCohomology.existsUnique_maximalSUnitsInflation_localization : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω)
        (a :
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
            Langlands.GaloisCohomology.LocalBrauerGroup v)
        (b : (w : NumberField.InfinitePlace K) → Langlands.GaloisCohomology.RealBrauerGroup w),
        {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | a v ≠ 0}.Finite →
          (∀ v ∉ S, a v = 0) →
            ∀ {k : ℕ},
              (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ℓ ^ k • a v = 0) →
                (∀ (w : NumberField.InfinitePlace K), ℓ ^ k • b w = 0) →
                  ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                          (Langlands.GaloisCohomology.finiteInvariant v) (a v) +
                        ∑ w : NumberField.InfinitePlace K, Langlands.GaloisCohomology.realInvariant w (b w) =
                      0 →
                    ∃! y :
                      ↥(AddCommGroup.primaryComponent
                          (↑(Langlands.ProfiniteCohomology.cohomology
                              (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2))
                          ℓ),
                      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                          (Langlands.GaloisCohomology.brauerLocalization ι v 2)
                              ((Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) ↑y) =
                            a v) ∧
                        ∀ (w : NumberField.InfinitePlace K),
                          (Langlands.GaloisCohomology.realBrauerLocalization ι w 2)
                              ((Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2) ↑y) =
                            b w
@Langlands.GaloisCohomology.exists_prime_nsmul_eq_cohomology_two_maximalSUnits : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ℓ ≠ 2 ∨ NumberField.IsTotallyComplex K →
        ∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)),
          ∃ (y' : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 2)),
            ℓ • y' = y
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §3, (8.3.11)
  Proposition (iii), p. 458; (8.3.12) Corollary (i), p. 459. NSW state (iii) as a kernel of the
  summation map on `⊕_{p ∈ S} Q_p/Z_p` (with `½Z/Z` at the real places for `p = 2`); here it is stated
  by global Brauer classes and their local classes.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/Brauer.lean` (lines 280–426). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source's
`sUnitsBrauer`, `exists_sUnitsBrauer_eq_iff`, `sUnitsBrauerPrimaryEquiv`, `sUnitsH2PrimaryEquiv` are
`maximalSUnitsInflation`, `exists_maximalSUnitsInflation_eq`, `maximalSUnitsPrimaryEquiv`,
`existsUnique_maximalSUnitsInflation_localization` (stated by local classes, not as an equivalence
with a direct sum); the surjectivity covers `ℓ = 2` with real components through
`Langlands.GaloisCohomology.Global.Units.ComplexRestriction`; the divisibility is new.
