# The divisor sequence of `K_S` prime to `S`

`Langlands/GaloisCohomology/Global/Units/DivisorSequence.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places, `G_S = Gal(K_S/K)`,
`ι : PlaceEmbeddings K Ω`, `D = sDivisorModule S ι` and `ℓ` a prime such that `S` contains the places
above `ℓ`.

- `sDivisorClassModule S ι`: the quotient `P` of `D` by the principal divisors
  (`sPrincipalDivisors`); every element is killed by an integer prime to `ℓ`
  (`exists_coprime_nsmul_sDivisorClass`, from `exists_coprime_nsmul_eq_unitsToSDivisor`).
- `sDivisorSequence_shortExact`: `0 → K_Sˣ/𝒪_Sˣ → D → P → 0` is exact (the kernel of the divisor map is
  `𝒪_Sˣ`).
- `exists_coprime_nsmul_cohomology_one_unitsModSUnits`: every class of `H¹(G_S, K_Sˣ/𝒪_Sˣ)` is killed by
  an integer prime to `ℓ` (`H¹(G_S, D) = 0`, so the class comes from `H⁰(G_S, P)`);
  `exists_coprime_nsmul_of_coeffMap_sDivisor_eq_zero`: the same for the kernel of
  `H²(G_S, K_Sˣ/𝒪_Sˣ) → H²(G_S, D)`.
- **Local class and order class over `G_S`** (`brauerLocalization_maximalUnitsInflation_eq_zero_iff`):
  for `z ∈ H²(G_S, K_Sˣ)` and `v ∉ S`, the localization at `v` of the inflation of `z` to
  `H²(Gal(Ω/K), Ωˣ)` vanishes if and only if the component at `v` of the image of `z` in `H²(G_S, D)`
  (a class of `H²(K_v, ℤ)`) does. Proof: `z` is inflated from a finite Galois level `E ⊆ K_S`
  (`unitsInflation_apply_eq` of `Langlands.GaloisCohomology.Global.BrauerSequence.FiniteComparison`);
  both sides are the maps of
  `Langlands.GaloisCohomology.Global.Units.LocalOrder` for the embedding of `E` given by `ι`
  (`brauerLocalization_maximalUnitsInflation_unitsTowerMap`,
  `map_divisorEval_unitsToSDivisor_unitsTowerMap`, `sOrder_units_map`), and the place is unramified.

The restriction to `ℓ`-primary parts in capitulation is removed in the module
`Langlands.GaloisCohomology.Global.Units.CapitulationPrincipalIdeal`, which imports the bridge
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal` to the principal ideal theorem of the NYLL copy:
for every finite level `L` of `K_S / K` there is a finite level `L' ⊇ L` in which every divisor of `L` prime
to `S` is the divisor of a unit (`exists_level_forall_unitsToSDivisor_eq`), so that, for every set `S` of
finite places and with no prime `ℓ`, the divisor map `K_Sˣ → Div_S(K_S)` is onto (`unitsToSDivisor_surjective`)
and the divisor class module is zero (`isZero_sDivisorClassModule`); `0 → 𝒪_Sˣ → K_Sˣ → D → 0` is then short
exact (`sUnitsDivisorSequence_shortExact`) and `K_Sˣ/𝒪_Sˣ → D` is an isomorphism
(`isIso_unitsModSUnitsToSDivisor`). In this file, which does not import the copy, the corresponding statements keep integers prime
to `ℓ` (`exists_coprime_nsmul_sDivisorClass`, `exists_coprime_nsmul_cohomology_one_unitsModSUnits`).

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.eq_zero_of_coprime_nsmul_eq_zero : ∀ {A : Type u_1} [inst : AddCommGroup A] {ℓ N k : ℕ},
  N.Coprime ℓ → ∀ {x : A}, N • x = 0 → ℓ ^ k • x = 0 → x = 0
@Langlands.GaloisCohomology.exists_primary_map_eq : ∀ {A : Type u_1} {B : Type u_2} [inst : AddCommGroup A]
  [inst_1 : AddCommGroup B] (f : A →+ B) {ℓ : ℕ},
  Nat.Prime ℓ →
    ∀ {y : A}, IsOfFinAddOrder y → ∀ {k : ℕ}, ℓ ^ k • f y = 0 → ∃ (y' : A), (∃ (j : ℕ), ℓ ^ j • y' = 0) ∧ f y' = f y
@Langlands.GaloisCohomology.sPrincipalDivisors : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                Submodule (ULift.{u_1, 0} ℤ) ↑(Langlands.GaloisCohomology.sDivisorModule S ι)
@Langlands.GaloisCohomology.mem_sPrincipalDivisors_iff : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (f : ↑(Langlands.GaloisCohomology.sDivisorModule S ι)),
  f ∈ Langlands.GaloisCohomology.sPrincipalDivisors S ι ↔
    ∃ (y : ↑(Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))),
      (Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) y = f
@Langlands.GaloisCohomology.sPrincipalDivisors_le_comap : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
  Langlands.GaloisCohomology.sPrincipalDivisors S ι ≤
    Submodule.comap ((Langlands.GaloisCohomology.sDivisorModule S ι).ρ g)
      (Langlands.GaloisCohomology.sPrincipalDivisors S ι)
@Langlands.GaloisCohomology.sDivisorClassModule : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
@Langlands.GaloisCohomology.sUnitsSubmodule_le_ker : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.GaloisCohomology.sUnitsSubmodule K Ω S ≤ (Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)).ker
@Langlands.GaloisCohomology.unitsModSUnitsToSDivisor : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                Langlands.GaloisCohomology.unitsModSUnitsModule K Ω S ⟶ Langlands.GaloisCohomology.sDivisorModule S ι
@Langlands.GaloisCohomology.unitsModSUnitsToSDivisor_mk : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (a : ↑(Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))),
  (Rep.Hom.hom (Langlands.GaloisCohomology.unitsModSUnitsToSDivisor S ι)) (Submodule.Quotient.mk a) =
    (Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) a
@Langlands.GaloisCohomology.sDivisorSequence : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                CategoryTheory.ShortComplex
                  (Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
@Langlands.GaloisCohomology.sDivisorSequence_shortExact : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω), (Langlands.GaloisCohomology.sDivisorSequence S ι).ShortExact
@Langlands.GaloisCohomology.isSmoothRep_sDivisorClassModule : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω), Langlands.IsSmoothRep (Langlands.GaloisCohomology.sDivisorClassModule S ι)
@Langlands.GaloisCohomology.isSmoothRep_sDivisorSequence_X₁ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω), Langlands.IsSmoothRep (Langlands.GaloisCohomology.sDivisorSequence S ι).X₁
@Langlands.GaloisCohomology.isSmoothRep_sDivisorSequence_X₂ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω), Langlands.IsSmoothRep (Langlands.GaloisCohomology.sDivisorSequence S ι).X₂
@Langlands.GaloisCohomology.isSmoothRep_sDivisorSequence_X₃ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω), Langlands.IsSmoothRep (Langlands.GaloisCohomology.sDivisorSequence S ι).X₃
@Langlands.GaloisCohomology.exists_coprime_nsmul_sDivisorClass : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (p : ↑(Langlands.GaloisCohomology.sDivisorClassModule S ι)), ∃ (N : ℕ), N.Coprime ℓ ∧ N • p = 0
@Langlands.GaloisCohomology.exists_coprime_nsmul_cohomology_one_unitsModSUnits : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModSUnitsModule K Ω S) 1)),
        ∃ (N : ℕ), N.Coprime ℓ ∧ N • x = 0
@Langlands.GaloisCohomology.exists_coprime_nsmul_of_coeffMap_sDivisor_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModSUnitsModule K Ω S) 2)),
        (ModuleCat.Hom.hom
                (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsModSUnitsToSDivisor S ι) 2))
              x =
            0 →
          ∃ (N : ℕ), N.Coprime ℓ ∧ N • x = 0
@Langlands.GaloisCohomology.map_map_apply : ∀ {k G H L : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : Group H] [inst_3 : Group L] [inst_4 : TopologicalSpace G] [inst_5 : TopologicalSpace H]
  [inst_6 : TopologicalSpace L] [inst_7 : IsTopologicalGroup G] [inst_8 : IsTopologicalGroup H]
  [inst_9 : IsTopologicalGroup L] {A : Rep.{u_1, u_1, u_1} k G} {B : Rep.{u_1, u_1, u_1} k H}
  {C : Rep.{u_1, u_1, u_1} k L} [inst_10 : Langlands.IsSmoothRep A] [inst_11 : Langlands.IsSmoothRep B]
  [inst_12 : Langlands.IsSmoothRep C] (φ : H →ₜ* G) (f : Rep.res (↑φ) A ⟶ B) (ψ : L →ₜ* H) (g : Rep.res (↑ψ) B ⟶ C)
  (n : ℕ) (x : ↑(Langlands.ProfiniteCohomology.cohomology A n)),
  (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map ψ g n))
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map φ f n)) x) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (φ.comp ψ) (CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑ψ).map f) g)
          n))
      x
@Langlands.GaloisCohomology.map_coeffMap_hom_apply : ∀ {k G H : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : Group H] [inst_3 : TopologicalSpace G] [inst_4 : TopologicalSpace H] [inst_5 : IsTopologicalGroup G]
  [inst_6 : IsTopologicalGroup H] {A : Rep.{u_1, u_1, u_1} k G} {B : Rep.{u_1, u_1, u_1} k H}
  [inst_7 : Langlands.IsSmoothRep A] [inst_8 : Langlands.IsSmoothRep B] (φ : H →ₜ* G) {A' : Rep.{u_1, u_1, u_1} k G}
  [inst_9 : Langlands.IsSmoothRep A'] (f : A ⟶ A') (g : Rep.res (↑φ) A' ⟶ B) (n : ℕ)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology A n)),
  (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map φ g n))
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap f n)) x) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map φ (CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑φ).map f) g) n))
      x
@Langlands.GaloisCohomology.sOrder_units_map : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ (L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) [inst_5 : FiniteDimensional K ↥L]
      (x : (↥L)ˣ),
      Langlands.GaloisCohomology.sOrder S ι v ((Units.map ↑L.val.toRingHom) x) =
        Langlands.GaloisCohomology.placeExponent v (Langlands.GaloisCohomology.levelEmbedding S ι v L) x
@Langlands.GaloisCohomology.normalKrullRestriction_localizationHom : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)),
  (Langlands.BrauerComparison.normalKrullRestriction K ↥E.toIntermediateField
        ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
      ((Langlands.Galois.localizationHom ι S ↑v) σ) =
    (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
        (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))
      σ
@Langlands.GaloisCohomology.brauerLocalization_maximalUnitsInflation_unitsTowerMap : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (b : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K ↥E.toIntermediateField) 2)),
  (Langlands.GaloisCohomology.brauerLocalization ι (↑v) 2)
      ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
        ((ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.unitsTowerMap K (↥E.toIntermediateField)
              (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
          b)) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map
          (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
            (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))
          (Langlands.GaloisCohomology.localUnitsHomOf (↑v)
            (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))
          2))
      b
@Langlands.GaloisCohomology.map_divisorEval_unitsToSDivisor_unitsTowerMap : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (b : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K ↥E.toIntermediateField) 2)),
  (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι v)
          (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
            (ULift.{u_1, 0} ℤ) v)
          2))
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
        ((ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.unitsTowerMap K (↥E.toIntermediateField)
              (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2))
          b)) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map
          (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
            (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))
          (Langlands.GaloisCohomology.localExponentHom (↑v)
            (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))
          2))
      b
@Langlands.GaloisCohomology.brauerLocalization_maximalUnitsInflation_eq_zero_iff : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (z :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)),
  (Langlands.GaloisCohomology.brauerLocalization ι (↑v) 2)
        ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2) z) =
      0 ↔
    (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι v)
            (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
              (ULift.{u_1, 0} ℤ) v)
            2))
        ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
          z) =
      0
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §3, (8.3.11)
  Proposition, p. 458 (the proof there uses `S`-idèle classes; here divisors are used).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BrauerDivisor.lean` (lines 109–175) and `Brauer.lean` (lines 16–280). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source's
`picInfRep`, `picSequence`, `sUnitsQuotDiv` are `sDivisorClassModule`, `sDivisorSequence`,
`unitsModSUnitsToSDivisor`; the comparison of local classes is new (it rests on
`Langlands.GaloisCohomology.Global.Units.LocalOrder`).
