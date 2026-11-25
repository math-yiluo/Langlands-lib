# Capitulation of divisors of `K_S` prime to `S`

`Langlands/GaloisCohomology/Global/Units/Capitulation.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places, `ℓ` a prime such that
every place above `ℓ` lies in `S`, and `ι : PlaceEmbeddings K Ω`.

**Theorem** (`exists_coprime_nsmul_eq_unitsToSDivisor`). For every divisor `f` of `K_S` prime to `S`
there are `N` prime to `ℓ` and `y ∈ K_Sˣ` with `div y = N • f`: the divisor class group of `K_S` prime to
`S` is killed, element by element, by integers prime to `ℓ`.

Proof. `IsCapitulating S ι ℓ f` says that some multiple of `f` by an integer prime to `ℓ` is principal;
it is stable under sums, integer multiples and translations (`isCapitulating_sum`,
`IsCapitulating.translate`). Every divisor is a finite sum of translates of divisors supported on one
orbit (`eq_sum_single`), and these are induced from a finite level (`isCapitulating_single_of_base`).
For a finite level `L ⊆ K_S` and a place `w` of `L` above `v ∉ S`, write `h·w = (y)` with `h` the class
number of `L` and `h = ℓ^a N`, `ℓ ∤ N`; then `N·w = (y^{1/ℓ^a})` in `K_S`, because the `ℓ^a`-th root
of `y` generates an extension unramified outside `S`
(`mem_maximalUnramifiedOutside_of_pow_eq_of_dvd`, Kummer theory with `ℓ` invertible outside `S`;
`isCapitulating_base`). This is the argument of NSW (8.3.4) (Kummer theory of `S`-units) applied to
divisors.

The restriction to `ℓ`-primary parts in capitulation is removed in the module
`Langlands.GaloisCohomology.Global.Units.CapitulationPrincipalIdeal`, which imports the bridge
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal` to the principal ideal theorem of the NYLL copy:
for every finite level `L` of `K_S / K` there is a finite level `L' ⊇ L` in which every divisor of `L` prime
to `S` is the divisor of a unit (`exists_level_forall_unitsToSDivisor_eq`), so that, for every set `S` of
finite places and with no prime `ℓ`, the divisor map `K_Sˣ → Div_S(K_S)` is onto (`unitsToSDivisor_surjective`)
and the divisor class module is zero (`isZero_sDivisorClassModule`); `0 → 𝒪_Sˣ → K_Sˣ → D → 0` is then short
exact (`sUnitsDivisorSequence_shortExact`) and `K_Sˣ/𝒪_Sˣ → D` is an isomorphism
(`isIso_unitsModSUnitsToSDivisor`). This file does not import the copy and keeps the restriction: it proves that multiples by
integers prime to `ℓ` of the divisors are principal, under its hypotheses on `ℓ` and `S`.

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.mem_maximalUnramifiedOutside_of_pow_eq_of_dvd : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {E : IntermediateField K Ω}
  [FiniteDimensional K ↥E] [inst_6 : NumberField ↥E],
  E ≤ Langlands.Galois.maximalUnramifiedOutside K Ω S →
    ∀ {n : ℕ},
      n ≠ 0 →
        (∀ v ∉ S, ↑n ∉ v.asIdeal) →
          ∀ (a : (↥E)ˣ),
            (∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E)),
                IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) w ∉ S →
                  ↑n ∣ ((IsDedekindDomain.HeightOneSpectrum.valuation (↥E) w) ↑a).log) →
              ∀ {α : Ω}, α ^ n = ↑↑a → α ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S
@Langlands.GaloisCohomology.IsCapitulating : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                ℕ →
                  ({ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
                      Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ) →
                    Prop
@Langlands.GaloisCohomology.isCapitulating_zero : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ℓ : ℕ), Langlands.GaloisCohomology.IsCapitulating S ι ℓ 0
@Langlands.GaloisCohomology.IsCapitulating.add : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ}
  {f g :
    { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
      Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ},
  Langlands.GaloisCohomology.IsCapitulating S ι ℓ f →
    Langlands.GaloisCohomology.IsCapitulating S ι ℓ g → Langlands.GaloisCohomology.IsCapitulating S ι ℓ (f + g)
@Langlands.GaloisCohomology.IsCapitulating.zsmul : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ}
  {f :
    { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
      Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ},
  Langlands.GaloisCohomology.IsCapitulating S ι ℓ f → ∀ (c : ℤ), Langlands.GaloisCohomology.IsCapitulating S ι ℓ (c • f)
@Langlands.GaloisCohomology.isCapitulating_sum : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ} {J : Type u_2} (T : Finset J)
  (f :
    J →
      { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
        Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ),
  (∀ i ∈ T, Langlands.GaloisCohomology.IsCapitulating S ι ℓ (f i)) →
    Langlands.GaloisCohomology.IsCapitulating S ι ℓ (∑ i ∈ T, f i)
@Langlands.GaloisCohomology.IsCapitulating.translate : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ}
  {f :
    { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
      Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ},
  Langlands.GaloisCohomology.IsCapitulating S ι ℓ f →
    ∀ (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
      Langlands.GaloisCohomology.IsCapitulating S ι ℓ
        fun (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
          (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) =>
        f v (x * g)
@Langlands.GaloisCohomology.decompositionSubgroup : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
                  Subgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
@Langlands.GaloisCohomology.zuInd : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
                  Subgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) →
                    Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ
@Langlands.GaloisCohomology.isCapitulating_single_of_base : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ}
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (U : Subgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [hUn : U.Normal],
  IsOpen ↑U →
    Langlands.GaloisCohomology.IsCapitulating S ι ℓ (Pi.single v (Langlands.GaloisCohomology.zuInd S ι v U)) →
      ∀ (φ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ),
        (∀ (x u : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S), u ∈ U → φ (x * u) = φ x) →
          (∀ z ∈ Langlands.GaloisCohomology.decompositionSubgroup S ι ↑v,
              ∀ (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S), φ (z * x) = φ x) →
            Langlands.GaloisCohomology.IsCapitulating S ι ℓ (Pi.single v φ)
@Langlands.GaloisCohomology.eq_sum_single : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (f :
    { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
      Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ)
  (T : Finset { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S }),
  (∀ v ∉ T, f v = 0) → f = ∑ v ∈ T, Pi.single v (f v)
@Langlands.GaloisCohomology.sOrder_pow : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ (y : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) (m : ℕ),
      Langlands.GaloisCohomology.sOrder S ι v (y ^ m) = ↑m * Langlands.GaloisCohomology.sOrder S ι v y
@Langlands.GaloisCohomology.levelRestrict_eq_one_of_mem : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  {u : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S},
  u ∈ L.fixingSubgroup → Langlands.GaloisCohomology.levelRestrict S L u = 1
@Langlands.GaloisCohomology.mem_decompositionSubgroup_mul_iff : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
  (∃ z ∈ Langlands.GaloisCohomology.decompositionSubgroup S ι v, ∃ u ∈ L.fixingSubgroup, g = z * u) ↔
    Langlands.GaloisCohomology.levelRestrict S L g ∈
      (↑(Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
            (Langlands.GaloisCohomology.levelEmbedding S ι v L.toIntermediateField))).range
@Langlands.GaloisCohomology.isCapitulating_base : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
        (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
        Langlands.GaloisCohomology.IsCapitulating S ι ℓ
          (Pi.single v (Langlands.GaloisCohomology.zuInd S ι v L.fixingSubgroup))
@Langlands.GaloisCohomology.exists_level_mul_eq : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [IsGalois K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (φ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ),
  IsLocallyConstant φ →
    ∃ (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
      ∀ (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S), ∀ u ∈ L.fixingSubgroup, φ (x * u) = φ x
@Langlands.GaloisCohomology.isCapitulating_single : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
        (φ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ),
        IsLocallyConstant φ →
          (∀
              (σ :
                Gal(AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
                      ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
              (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
              φ ((Langlands.Galois.localizationHom ι S ↑v) σ * x) = φ x) →
            Langlands.GaloisCohomology.IsCapitulating S ι ℓ (Pi.single v φ)
@Langlands.GaloisCohomology.exists_coprime_nsmul_eq_unitsToSDivisor : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (f : ↑(Langlands.GaloisCohomology.sDivisorModule S ι)),
        ∃ (N : ℕ),
          N.Coprime ℓ ∧
            ∃ (y : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ),
              (Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) (Additive.ofMul y) = N • f
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §3, (8.3.4)
  Proposition, pp. 453–454 (Kummer theory of `S`-units: `ℓ`-th roots of `S`-units lie in `K_S`).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BrauerDivisor.lean` (lines 176–546). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source's
`Good`, `good_single_of_base`, `good_base`, `exists_coprime_smul_picInfRep` are `IsCapitulating`,
`isCapitulating_single_of_base`, `isCapitulating_base`, `exists_coprime_nsmul_eq_unitsToSDivisor`.
