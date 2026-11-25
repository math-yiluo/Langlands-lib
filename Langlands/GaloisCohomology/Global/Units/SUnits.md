# `S`-units as Galois modules, and their invariants

`Langlands/GaloisCohomology/Global/Units/SUnits.lean`, namespace `Langlands.GaloisCohomology`.

Let `F` be a number field, `S` a set of finite places of `F` and `E` a field over `F`. The
`S`-units of `E` (`sUnitsOf S E`) are the units `x` such that `x` and `x⁻¹` are integral over the
`S`-integers `S.integer F` of `F` (Mathlib's `Set.integer`). For a number field `L` over `F` they are
Mathlib's `Set.unit` for the set `finitePlacesAbove L S` of places of `L` above `S`
(`mem_sUnitsOf_iff_mem_unit`). The Galois action preserves them, and `sUnitsModule S E` is the
smooth `Gal(E / F)`-module of `S`-units (over `ULift ℤ`, as the foundations' units module); for
`E / F` Galois its invariants are the `S`-units of `F` (`sUnitsInvariantsEquiv`), i.e.
`H⁰(Gal(E/F), 𝒪_{E,S}ˣ) = 𝒪_{F,S}ˣ` (`cohomologyZeroSUnitsEquiv`). For `Ω / F` Galois,
`maximalSUnitsModule F Ω S` is the `G_S`-module `𝒪_Sˣ` of `S`-units of `K_S`; every one of them is
an `S`-unit of a finite subextension (`exists_of_mem_maximalSUnits`).

**Roots in `K_S`.** If `M = K(α)` with `αⁿ = a ∈ Kˣ`, `n` is prime to a finite place `v` and `n`
divides the valuation of `a` at `v`, then every prime of `M` above `v` is unramified
(`isUnramifiedAt_of_pow_eq`): after multiplying `a` by an `n`-th power one may assume `a` is a
`v`-adic unit, and then `α` is a root of `Xⁿ - a`, whose derivative `nαⁿ⁻¹` is a unit at every prime
above `v`. Consequently, if `n` is invertible outside `S`, the `n`-th roots of `S`-units of `K_S`
(in particular the `n`-th roots of unity) lie in `K_S` (`mem_maximalUnramifiedOutside_of_pow_eq`,
`_one`), and when `Ω` is separably closed every `S`-unit of `K_S` is the `n`-th power of an `S`-unit
of `K_S` (`exists_pow_eq_of_mem_maximalSUnits`).

The file also has the units `placeUnit v` generating the principal ideal `v^{h_F}` (`h_F` the class
number), with valuation `-h_F` at `v` and `0` elsewhere (`valuationOfNeZero_placeUnit`).

## Complete types

```lean
@Langlands.GaloisCohomology.sUnitsOf : {F : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
        (E : Type u_1) → [inst_2 : Field E] → [Algebra F E] → Subgroup Eˣ

@Langlands.GaloisCohomology.sUnitsModule : {F : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
        (E : Type u_1) → [inst_2 : Field E] → [inst_3 : Algebra F E] → Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(E/F)

Langlands.GaloisCohomology.maximalSUnitsModule : (F : Type u_1) →
  [inst : Field F] →
    [NumberField F] →
      (Ω : Type u_1) →
        [inst_2 : Field Ω] →
          [inst_3 : Algebra F Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
              Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside F Ω S)

@Langlands.GaloisCohomology.mem_sUnitsOf_iff_mem_unit : ∀ {F : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  {L : Type u_1} [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra F L]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) {x : Lˣ},
  x ∈ Langlands.GaloisCohomology.sUnitsOf S L ↔ x ∈ (Langlands.Galois.finitePlacesAbove L S).unit L

@Langlands.GaloisCohomology.sUnitsInvariantsEquiv : {F : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
        (E : Type u_1) →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              [IsGalois F E] → Additive ↥(S.unit F) ≃+ ↥(Langlands.GaloisCohomology.sUnitsModule S E).ρ.invariants

@Langlands.GaloisCohomology.cohomologyZeroSUnitsEquiv : {F : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
        (E : Type u_1) →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              [inst_4 : IsGalois F E] →
                ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.sUnitsModule S E) 0) ≃+
                  Additive ↥(S.unit F)

@Langlands.GaloisCohomology.isUnramifiedAt_of_pow_eq : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  {M : Type u_2} [inst_2 : Field M] [NumberField M] [inst_4 : Algebra K M] {n : ℕ} (a : Kˣ) {α : M},
  α ^ n = (algebraMap K M) ↑a →
    K⟮α⟯ = ⊤ →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ↑n ∉ v.asIdeal →
          ↑n ∣ ((IsDedekindDomain.HeightOneSpectrum.valuation K v) ↑a).log →
            ∀ (P : Ideal (NumberField.RingOfIntegers M)) [inst_5 : P.IsPrime] [P.LiesOver v.asIdeal],
              Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P

@Langlands.GaloisCohomology.mem_maximalUnramifiedOutside_of_pow_eq : ∀ {F : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] {Ω : Type u_1} [inst_2 : Field Ω] [inst_3 : Algebra F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [IsGalois F Ω] {n : ℕ},
  n ≠ 0 →
    (∀ v ∉ S, ↑n ∉ v.asIdeal) →
      ∀ {y : (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))ˣ},
        y ∈ Langlands.GaloisCohomology.maximalSUnits F Ω S →
          ∀ {α : Ω}, α ^ n = ↑↑y → α ∈ Langlands.Galois.maximalUnramifiedOutside F Ω S

@Langlands.GaloisCohomology.exists_pow_eq_of_mem_maximalSUnits : ∀ {F : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] {Ω : Type u_1} [inst_2 : Field Ω] [inst_3 : Algebra F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [IsGalois F Ω] [IsSepClosed Ω] {n : ℕ},
  n ≠ 0 →
    (∀ v ∉ S, ↑n ∉ v.asIdeal) →
      ∀ {y : (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))ˣ},
        y ∈ Langlands.GaloisCohomology.maximalSUnits F Ω S →
          ∃ β ∈ Langlands.GaloisCohomology.maximalSUnits F Ω S, β ^ n = y
```

The roots of unity of `K_S`: `card_rootsOfUnity_maximalUnramifiedOutside hS`: when `S` contains the
places above `N`, `K_S` contains `N` distinct `N`-th roots of unity; `exists_isPrimitiveRoot_mem hS`: it
contains a primitive `q`-th root of unity.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.card_rootsOfUnity_maximalUnramifiedOutside.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) :
  Nat.card ↥(rootsOfUnity N ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) = N
Langlands.GaloisCohomology.exists_isPrimitiveRoot_mem.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (q : ℕ)
  [NeZero q] (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑q ∈ v.asIdeal → v ∈ S) :
  ∃ ζ, IsPrimitiveRoot ζ q ∧ ζ ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S
```

## Outline of the proofs

`mem_sUnitsOf_iff_mem_unit`: an element integral over the `S`-integers has valuation `≤ 1` at the
places not above `S` (`valuation_le_one_of_isIntegral_integer`, valuations of integral elements);
conversely an element of valuation `≤ 1` outside `S` becomes an algebraic integer after
multiplication by a power of the `S`-unit `∏ placeUnit v` over the places `v ∈ S` under its poles
(`isIntegral_integer_of_valuation_le_one`). The invariants: an invariant element of `E` lies in `F`
(Galois theory, `InfiniteGalois.mem_range_algebraMap_iff_fixed`) and is an `S`-unit there
(`map_mem_sUnitsOf_iff`). `mem_maximalUnramifiedOutside_of_pow_eq`: `y` lies in a finite
subextension `L ⊆ K_S`, its `n`-th root generates `L(α)` unramified over `L` outside the places
above `S` by Kummer, hence `L(α)` is unramified outside `S` over `F`
(`isUnramifiedOutside_restrictScalars_iff` of `Langlands/Galois/RestrictedRamification/Unramified.lean`).

## Declarations

`valuation_le_one_of_isIntegral`, `exists_mul_pow_le_one`, `exists_pow_classNumber_eq_span`,
`intValuation_of_pow_eq_span`, `placeUnit`, `valuationOfNeZero_placeUnit`, `placeUnit_mem`,
`exists_mul_pow_integral_notMem`, `isUnramifiedAt_of_pow_eq`, `ramificationIdx_eq_one_of_pow_eq`,
`isUnramifiedIn_of_pow_eq`, `sUnitsOf`, `mem_sUnitsOf`, `isIntegral_algEquiv_apply`,
`mem_sUnitsOf_of_mem_rootsOfUnity`, `galUnitsHom_mem_sUnitsOf`, `sUnitsAction`,
`coe_sUnitsAction_apply`, `sUnitsModule`, `sUnitsModule_ρ_apply`, `sUnitsToUnits`,
`sUnitsToUnits_hom_apply`, `sUnitsToUnits_injective`, `isSmoothRep_sUnitsModule`,
`rootsOfUnityToSUnitsHom`, `rootsOfUnityToSUnits`, `rootsOfUnityToSUnits_hom_apply`,
`maximalSUnits`, `maximalSUnitsModule`, `liesOver_under`, `valuation_algebraMap_integer_le_one`,
`valuation_le_one_of_isIntegral_integer`, `isIntegral_integer_of_valuation_le_one`,
`mem_sUnitsOf_iff_mem_unit`, `isIntegral_algebraMap_of_mem_integer`,
`isIntegral_of_isIntegral_algebraMap`, `mem_integer_of_isIntegral`, `map_mem_sUnitsOf_iff`,
`sUnitsToInvariants`, `coe_sUnitsToInvariants_apply`, `sUnitsToInvariants_injective`,
`sUnitsToInvariants_surjective`, `sUnitsInvariantsEquiv`, `sUnitsInvariantsEquiv_apply`,
`cohomologyZeroSUnitsEquiv`, `map_inclusion_mem_maximalSUnits_iff`, `exists_of_mem_maximalSUnits`,
`adjoin_gen_eq_top`, `mem_maximalUnramifiedOutside_of_pow_eq`,
`mem_maximalUnramifiedOutside_of_pow_eq_one`, `mem_sUnitsOf_of_pow_mem`,
`exists_pow_eq_of_mem_maximalSUnits`, `card_rootsOfUnity_maximalUnramifiedOutside`, `exists_isPrimitiveRoot_mem`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files (under
`src/GroundTheory/`) `ProfiniteCohomology/RestrictedRamification/SUnitsDefs.lean` (lines 13–119 and
137–150, without the Kummer sequence), `ProfiniteCohomology/RestrictedRamification/SUnits.lean`
(lines 15–387, without the exactness of the Kummer sequence), `GlobalFields/SUnits.lean` (lines
15–70) and `GlobalFields/KummerTheory/Unramified.lean` (lines 11–128; the design's "one Kummer lemma
on ramification", (I8), not class field theory). The repository has no licence file; its text is
used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).
Changes: `galSUnits`, `galSUnitsHom`, `sUnitsMax`, `galSUnitsMax`, `h0SUnitsEquiv` are
`sUnitsModule`, `sUnitsAction`, `maximalSUnits`, `maximalSUnitsModule`, `cohomologyZeroSUnitsEquiv`;
the source's `underPlace` and `placesOver` are Mathlib's `HeightOneSpectrum.under` and Stage 1's
`finitePlacesAbove`; the foundations' `unitsModule`, `zeroIso`, `IsSmoothRep` replace `galUnits`,
`H0Iso`, `IsDiscreteRep`; `multiplicity_eq_zero` is replaced by `multiplicity_eq_zero_of_not_dvd`.

`card_rootsOfUnity_maximalUnramifiedOutside` comes with the text that the licence record lists for
`GlobalEulerCharacteristic/ShaCount.lean` lines 60–98 of the repository; `exists_isPrimitiveRoot_mem`
contains no text of the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): chapter VIII, §3, Proposition (8.3.4), p. 453 (`μ_n ⊆ k_S` and
  `n`-divisibility of `𝒪_Sˣ` for `n` invertible outside `S`) and Proposition (8.3.11) (i), p. 458
  (`H⁰(G_S, 𝒪_Sˣ) = 𝒪_{k,S}ˣ`).
