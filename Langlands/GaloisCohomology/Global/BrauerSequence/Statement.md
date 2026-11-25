# The fundamental exact sequence of the Brauer group of a number field: statement

`Langlands/GaloisCohomology/Global/BrauerSequence/Statement.lean`, namespace
`Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure of `K` (in the universe of `K`) and
`ι : PlaceEmbeddings K Ω` a choice of embeddings of `Ω` into the algebraic closures of the
completions of `K`. The Brauer group of `K` is `H²(Gal(Ω/K), Ωˣ)` (the foundations' cochain model;
`unitsModule K Ω` is `Ωˣ` with the Galois action, over `ULift ℤ`).

**Localization and local invariants.** At a finite place `v`, `brauerLocalization ι v n` is the map
`Hⁿ(Gal(Ω/K), Ωˣ) → Hⁿ(Gal(K̄_v/K_v), K̄_vˣ)` along the decomposition homomorphism of `ι.finite v`,
with coefficients `x ↦ ι.finite v x` (`unitsLocalHom`); at an infinite place `w`,
`realBrauerLocalization ι w n` likewise. `finiteInvariant v : H²(K_v, K̄_vˣ) ≃+ ℚ/ℤ` is the local
theory's invariant (`Local.invariant`, i.e. the Library's `localBrauerInvariant` through
`Br(K_v) ≅ H²`) for the completion with its own topology and valuation; `realInvariant w` is `1/2` on
a nonzero class and `0` on the zero class (the group has at most two elements, and none but `0` at a
complex place). `localInvariant ι v` and `realLocalInvariant ι w` are the composites.

**`BrauerSequenceData K Ω ι`** collects:

- (I1) `finite_support`: only finitely many `brauerLocalization ι v 2 x` are nonzero;
  `eq_zero_of_brauerLocalization_eq_zero`: a class with all localizations zero is zero;
  `sum_localInvariant_eq_zero`: `∑ᶠ_v inv_v(x) + ∑_w inv_w(x) = 0` (reciprocity law);
  `existsUnique_brauerLocalization_eq`: a family of local classes, finitely supported at the finite
  places, whose invariants sum to zero is the family of localizations of a unique global class;
- (I2) `subsingleton_cohomology_three`: `H³(Gal(Ω/K), Ωˣ) = 0`;
  `bijective_realBrauerLocalization`: for `r ≥ 4`, `Hʳ(Gal(Ω/K), Ωˣ) → ∏_{w real} Hʳ(K_w, K̄_wˣ)` is
  bijective;
- (I3) `brauerRestriction_eq_zero`: if `m • x = 0`, the real localizations of `x` vanish, and
  `m ∣ [E_w : K_v]` (`localDegree`) for every place `w` of a finite extension `E ⊆ Ω` above a finite
  place `v` at which `x` is nonzero, then the restriction of `x` to `Gal(Ω/E)` (`brauerRestriction`)
  is zero;
- (I4) `exists_isCyclic_dvd_localDegree`: for a finite set `T` of finite places and `m ≠ 0` there is
  a finite Galois extension `E ⊆ Ω` of `K` with cyclic Galois group and `m ∣ [E_w : K_v]` for all
  `v ∈ T` and `w ∣ v`.

`BrauerSequenceStatement` asserts `BrauerSequenceData K Ω ι` for all `K`, `Ω`, `ι` (in one universe
`u`). Stated from the data: injectivity of the localization to all places
(`brauerLocalization_injective`), finiteness of the support of the invariants
(`finite_support_localInvariant`), the vanishing criterion by invariants
(`eq_zero_iff_localInvariant`), existence of a global class with prescribed localizations
(`exists_brauerLocalization_eq`), and `Hʳ(Gal(Ω/K), Ωˣ) = 0` for `r ≥ 3` when `K` is totally
complex (`subsingleton_cohomology_of_three_le`).

## Complete types

```lean
structure Langlands.GaloisCohomology.BrauerSequenceData.{u} (K Ω : Type u) [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) : Prop
number of parameters: 8
fields:
  Langlands.GaloisCohomology.BrauerSequenceData.finite_support : ∀
      (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
      {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
          (Langlands.GaloisCohomology.brauerLocalization ι v 2) x ≠ 0}.Finite
  Langlands.GaloisCohomology.BrauerSequenceData.eq_zero_of_brauerLocalization_eq_zero : ∀
      (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          (Langlands.GaloisCohomology.brauerLocalization ι v 2) x = 0) →
        (∀ (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x = 0) → x = 0
  Langlands.GaloisCohomology.BrauerSequenceData.sum_localInvariant_eq_zero : ∀
      (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
      ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
            (Langlands.GaloisCohomology.localInvariant ι v) x +
          ∑ w : NumberField.InfinitePlace K, Langlands.GaloisCohomology.realLocalInvariant ι w x =
        0
  Langlands.GaloisCohomology.BrauerSequenceData.existsUnique_brauerLocalization_eq : ∀
      (a :
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
          Langlands.GaloisCohomology.LocalBrauerGroup v)
      (b : (w : NumberField.InfinitePlace K) → Langlands.GaloisCohomology.RealBrauerGroup w),
      {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | a v ≠ 0}.Finite →
        ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                (Langlands.GaloisCohomology.finiteInvariant v) (a v) +
              ∑ w : NumberField.InfinitePlace K, Langlands.GaloisCohomology.realInvariant w (b w) =
            0 →
          ∃! x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2),
            (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                (Langlands.GaloisCohomology.brauerLocalization ι v 2) x = a v) ∧
              ∀ (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x = b w
  Langlands.GaloisCohomology.BrauerSequenceData.subsingleton_cohomology_three : Subsingleton
      ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 3)
  Langlands.GaloisCohomology.BrauerSequenceData.bijective_realBrauerLocalization : ∀ (r : ℕ),
      4 ≤ r →
        Function.Bijective
          fun (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) r))
            (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
          (Langlands.GaloisCohomology.realBrauerLocalization ι (↑w) r) x
  Langlands.GaloisCohomology.BrauerSequenceData.brauerRestriction_eq_zero : ∀ (E : IntermediateField K Ω)
      [inst : FiniteDimensional K ↥E]
      (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)) (m : ℕ),
      m • x = 0 →
        (∀ (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x = 0) →
          (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
              (Langlands.GaloisCohomology.brauerLocalization ι v 2) x ≠ 0 →
                ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E))
                  [inst_1 : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree E v w) →
            (Langlands.GaloisCohomology.brauerRestriction E) x = 0
  Langlands.GaloisCohomology.BrauerSequenceData.exists_isCyclic_dvd_localDegree : ∀
      (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (m : ℕ),
      m ≠ 0 →
        ∃ (E : IntermediateField K Ω) (x : FiniteDimensional K ↥E),
          IsGalois K ↥E ∧
            IsCyclic Gal(↥E/K) ∧
              ∀ v ∈ T,
                ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E))
                  [inst : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree E v w
```

```lean
@Langlands.GaloisCohomology.LocalBrauerGroup : {K : Type u_1} →
  [inst : Field K] → [NumberField K] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Type u_1

@Langlands.GaloisCohomology.RealBrauerGroup : {K : Type u_1} → [inst : Field K] → NumberField.InfinitePlace K → Type u_1

@Langlands.GaloisCohomology.finiteInvariant : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        Langlands.GaloisCohomology.LocalBrauerGroup v ≃+ Langlands.ClassFieldTheory.Local.RationalModIntegers

@Langlands.GaloisCohomology.realInvariant : {K : Type u_1} →
  [inst : Field K] →
    (w : NumberField.InfinitePlace K) →
      Langlands.GaloisCohomology.RealBrauerGroup w → Langlands.ClassFieldTheory.Local.RationalModIntegers

@Langlands.GaloisCohomology.realInvariant_eq_zero_iff : ∀ {K : Type u_1} [inst : Field K]
  (w : NumberField.InfinitePlace K) (y : Langlands.GaloisCohomology.RealBrauerGroup w),
  Langlands.GaloisCohomology.realInvariant w y = 0 ↔ y = 0

@Langlands.GaloisCohomology.unitsLocalHom : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                Rep.res
                    (↑(Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                        (ι.finite v)))
                    (Langlands.GaloisCohomology.unitsModule K Ω) ⟶
                  Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))

@Langlands.GaloisCohomology.brauerLocalization : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            Langlands.Galois.PlaceEmbeddings K Ω →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                (n : ℕ) →
                  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) n) →+
                    ↑(Langlands.ProfiniteCohomology.cohomology
                        (Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
                        n)

@Langlands.GaloisCohomology.realBrauerLocalization : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            Langlands.Galois.PlaceEmbeddings K Ω →
              (w : NumberField.InfinitePlace K) →
                (n : ℕ) →
                  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) n) →+
                    ↑(Langlands.ProfiniteCohomology.cohomology
                        (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) n)

@Langlands.GaloisCohomology.localInvariant : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            Langlands.Galois.PlaceEmbeddings K Ω →
              IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
                ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2) →+
                  Langlands.ClassFieldTheory.Local.RationalModIntegers

@Langlands.GaloisCohomology.realLocalInvariant : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            Langlands.Galois.PlaceEmbeddings K Ω →
              NumberField.InfinitePlace K →
                ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2) →
                  Langlands.ClassFieldTheory.Local.RationalModIntegers

@Langlands.GaloisCohomology.brauerRestriction : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            (E : IntermediateField K Ω) →
              ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2) →+
                ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule (↥E) Ω) 2)

@Langlands.GaloisCohomology.localDegree : {K Ω : Type u_1} →
  [inst : Field K] →
    [NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (E : IntermediateField K Ω) →
            [FiniteDimensional K ↥E] →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E)) →
                  [w.asIdeal.LiesOver v.asIdeal] → ℕ

Langlands.GaloisCohomology.BrauerSequenceStatement : Prop

@Langlands.GaloisCohomology.BrauerSequenceData.brauerLocalization_injective : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω},
  Langlands.GaloisCohomology.BrauerSequenceData K Ω ι →
    Function.Injective
      fun (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)) =>
      (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) =>
        (Langlands.GaloisCohomology.brauerLocalization ι v 2) x, fun (w : NumberField.InfinitePlace K) =>
        (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x)

@Langlands.GaloisCohomology.BrauerSequenceData.finite_support_localInvariant : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω},
  Langlands.GaloisCohomology.BrauerSequenceData K Ω ι →
    ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
      (Function.support fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) =>
          (Langlands.GaloisCohomology.localInvariant ι v) x).Finite

@Langlands.GaloisCohomology.BrauerSequenceData.eq_zero_iff_localInvariant : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω},
  Langlands.GaloisCohomology.BrauerSequenceData K Ω ι →
    ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
      x = 0 ↔
        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
            (Langlands.GaloisCohomology.localInvariant ι v) x = 0) ∧
          ∀ (w : NumberField.InfinitePlace K), Langlands.GaloisCohomology.realLocalInvariant ι w x = 0

@Langlands.GaloisCohomology.BrauerSequenceData.exists_brauerLocalization_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω},
  Langlands.GaloisCohomology.BrauerSequenceData K Ω ι →
    ∀
      (a :
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
          Langlands.GaloisCohomology.LocalBrauerGroup v)
      (b : (w : NumberField.InfinitePlace K) → Langlands.GaloisCohomology.RealBrauerGroup w),
      {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | a v ≠ 0}.Finite →
        ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                (Langlands.GaloisCohomology.finiteInvariant v) (a v) +
              ∑ w : NumberField.InfinitePlace K, Langlands.GaloisCohomology.realInvariant w (b w) =
            0 →
          ∃ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
            (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                (Langlands.GaloisCohomology.brauerLocalization ι v 2) x = a v) ∧
              ∀ (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x = b w

@Langlands.GaloisCohomology.BrauerSequenceData.subsingleton_cohomology_of_three_le : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω},
  Langlands.GaloisCohomology.BrauerSequenceData K Ω ι →
    (∀ (w : NumberField.InfinitePlace K), w.IsComplex) →
      ∀ {r : ℕ},
        3 ≤ r → Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) r)
```

`realInvariant_zero_apply w`: the real invariant of the zero family vanishes.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.realInvariant_zero_apply.{u} {K : Type u} [Field K] (w : NumberField.InfinitePlace K) :
  Langlands.GaloisCohomology.realInvariant w (0 w) = 0
```

## Outline of the proofs

The theorems of the file are formal consequences of the fields: injectivity from
`eq_zero_of_brauerLocalization_eq_zero` applied to a difference; the support of the invariants from
`finite_support` and the bijectivity of `finiteInvariant`; the case of a totally complex field from
`bijective_realBrauerLocalization` with an empty set of real places. The fields (I1), (I3) and
(I4) are proved in `BrauerSequence/Proof.lean` from the Library's global class field theory at
finite levels, the two fields of (I2) being a hypothesis there
(`UnitsCohomologyHigherDegreesStatement`); that hypothesis is proved in `BrauerSequence/HigherDegrees.lean`
(`unitsCohomologyHigherDegreesStatement`), which gives `brauerSequenceStatement`.

## Declarations

`charZero_adicCompletion'`, `charZero_infinitePlaceCompletion`, `LocalBrauerGroup`,
`RealBrauerGroup`, `finiteInvariant`, `realInvariant`, `realInvariant_zero`,
`realInvariant_eq_zero_iff`, `unitsLocalHom`, `unitsLocalHom_hom_apply`, `realUnitsLocalHom`,
`brauerLocalization`, `realBrauerLocalization`, `localInvariant`, `realLocalInvariant`,
`localInvariant_apply`, `localInvariant_eq_zero_iff`, `realLocalInvariant_eq_zero_iff`,
`brauerRestriction`, `localDegree`, `BrauerSequenceData`, `BrauerSequenceStatement`,
`BrauerSequenceData.brauerLocalization_injective`,
`BrauerSequenceData.finite_support_localInvariant`, `BrauerSequenceData.eq_zero_iff_localInvariant`,
`BrauerSequenceData.exists_brauerLocalization_eq`,
`BrauerSequenceData.subsingleton_cohomology_of_three_le`, `realInvariant_zero_apply`.

## Source and licence

New file. Its statements correspond to declarations of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`, under `src/GroundTheory/ProfiniteCohomology/GlobalClassFormation/`, which it
restates and does not copy: `brauerLocal`, `placeInv`, `sumPlaceInv`
(`EqZeroOfBrauerLocalApplyEqZero.lean`, `LocalInvariants.lean`), `brauerLocal_injective`,
`brauerSumInv_eq_zero` (`SumInvariants.lean`), `sumPlaceInv_eq_zero_iff`
(`ExistsUnitsToIdelesEqOfIdelesSumInvEqZero.lean`), `subsingleton_cohomology_three_unitsLimitRep`
(`../GlobalClassFormation.lean`), `bijective_realLocalization`,
`subsingleton_cohomology_unitsLimitRep_of_three_le` (`HighUnits.lean`),
`unitsResField_eq_zero_of_dvd_finrank` (`Splitting.lean`), `exists_cyclic_layer_dvd_localDegree`
(`LocalDegrees.lean`). Changes against the source: a number field `K : Type u` with any separable
closure `Ω` replaces the subfields of `AlgebraicClosure ℚ`; the localization is to the completions'
absolute Galois groups through `PlaceEmbeddings`; the local invariant at the finite places is the
Library's (`Local.invariant`); the cyclic extension of (I4) is not required to lie in a cyclotomic
extension.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): chapter VIII, §1: Theorem (8.1.17), p. 437 (the exact sequence
  `0 → Br(k) → ⊕_p Br(k_p) → ℚ/ℤ → 0`, with the sum of the local invariants); Corollary (8.1.3),
  p. 428 (`H³(G, I_K) = 0` at a finite Galois level) and Proposition (8.1.20), p. 439 (exactness of
  `0 → H²(k, k̄ˣ) → H²(k, I) → H²(k, C) → 0`), from which `H³(k, k̄ˣ) = 0` follows.
