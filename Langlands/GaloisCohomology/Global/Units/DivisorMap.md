# The divisor map of `K_S` prime to `S`

`Langlands/GaloisCohomology/Global/Units/DivisorMap.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω / K` Galois (a separable closure in the applications), `S` a set of
finite places, `K_S ⊆ Ω` the maximal subextension unramified outside `S` and
`ι : PlaceEmbeddings K Ω`. For `v ∉ S` the embedding `ι.finite v` defines a place of every finite
subextension `L` of `K_S / K` (that of `levelEmbedding S ι v L`); these places are compatible in
towers, and since `K_S / K` is unramified at `v` (`isUnramifiedIn_of_maximalUnramifiedOutside`) so
are the normalized valuations.

- `sOrder S ι v : K_Sˣ → ℤ` is the exponent of the valuation at the place of `ι` above `v`, computed in
  any finite subextension containing the unit (`sOrder_eq`); it is additive (`sOrder_mul`) and
  invariant under `localizationHom ι S v` (`sOrder_localizationHom`).
- `sDivisorModule S ι` is the divisor module (`divisorModule`) of the family of localization maps at
  the places outside `S`, with coefficients `ℤ`.
- `unitsToSDivisor S ι : K_Sˣ → sDivisorModule S ι`, `x ↦ ((v, g) ↦ sOrder S ι v (g x))`, is a morphism of
  `G_S`-modules; its kernel is the group of `S`-units of `K_S` (`unitsToSDivisor_eq_zero_iff`).

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.isUnramifiedIn_of_maximalUnramifiedOutside : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) [FiniteDimensional K ↥L]
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S → Algebra.IsUnramifiedIn (NumberField.RingOfIntegers ↥L) v.asIdeal
@Langlands.GaloisCohomology.levelEmbedding : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
            Langlands.Galois.PlaceEmbeddings K Ω →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                (L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) →
                  ↥L →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
@Langlands.GaloisCohomology.levelUnit : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field Ω] →
      [inst_2 : Algebra K Ω] →
        {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
          {L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)} →
            (x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) → ↑x ∈ L → (↥L)ˣ
@Langlands.GaloisCohomology.coe_levelUnit : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  {L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
  (x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) (hx : ↑x ∈ L),
  ↑↑(Langlands.GaloisCohomology.levelUnit x hx) = ↑x
@Langlands.GaloisCohomology.finiteDimensional_adjoin_maximal : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] [IsGalois K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (x : ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)), FiniteDimensional K ↥K⟮x⟯
@Langlands.GaloisCohomology.sOrder : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
                  (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ → ℤ
@Langlands.GaloisCohomology.placeExponent_levelUnit_of_le : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ {L₁ L₂ : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
      [inst_5 : FiniteDimensional K ↥L₁] [inst_6 : FiniteDimensional K ↥L₂] (h : L₁ ≤ L₂)
      (x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) (hx₁ : ↑x ∈ L₁),
      Langlands.GaloisCohomology.placeExponent v (Langlands.GaloisCohomology.levelEmbedding S ι v L₂)
          (Langlands.GaloisCohomology.levelUnit x ⋯) =
        Langlands.GaloisCohomology.placeExponent v (Langlands.GaloisCohomology.levelEmbedding S ι v L₁)
          (Langlands.GaloisCohomology.levelUnit x hx₁)
@Langlands.GaloisCohomology.sOrder_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ {L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)} [inst_5 : FiniteDimensional K ↥L]
      (x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) (hx : ↑x ∈ L),
      Langlands.GaloisCohomology.sOrder S ι v x =
        Langlands.GaloisCohomology.placeExponent v (Langlands.GaloisCohomology.levelEmbedding S ι v L)
          (Langlands.GaloisCohomology.levelUnit x hx)
@Langlands.GaloisCohomology.sOrder_mul : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ (x y : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ),
      Langlands.GaloisCohomology.sOrder S ι v (x * y) =
        Langlands.GaloisCohomology.sOrder S ι v x + Langlands.GaloisCohomology.sOrder S ι v y
@Langlands.GaloisCohomology.sOrder_one : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S → Langlands.GaloisCohomology.sOrder S ι v 1 = 0
@Langlands.GaloisCohomology.levelUnit_mem_sUnitsOf : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  {L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
  {x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ} (hx : ↑x ∈ L),
  x ∈ Langlands.GaloisCohomology.maximalSUnits K Ω S →
    Langlands.GaloisCohomology.levelUnit x hx ∈ Langlands.GaloisCohomology.sUnitsOf S ↥L
@Langlands.GaloisCohomology.mem_maximalSUnits_of_levelUnit : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  {L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
  {x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ} (hx : ↑x ∈ L),
  Langlands.GaloisCohomology.levelUnit x hx ∈ Langlands.GaloisCohomology.sUnitsOf S ↥L →
    x ∈ Langlands.GaloisCohomology.maximalSUnits K Ω S
@Langlands.GaloisCohomology.sOrder_eq_zero_of_mem : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ {x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ},
      x ∈ Langlands.GaloisCohomology.maximalSUnits K Ω S → Langlands.GaloisCohomology.sOrder S ι v x = 0
@Langlands.GaloisCohomology.levelRestrict : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field Ω] →
      [inst_2 : Algebra K Ω] →
        (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
          (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) →
            Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → Gal(↥L.toIntermediateField/K)
@Langlands.GaloisCohomology.levelRestrict_apply : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (z : ↥L.toIntermediateField),
  ↑((Langlands.GaloisCohomology.levelRestrict S L g) z) = g ↑z
@Langlands.GaloisCohomology.levelUnit_galUnitsHom : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) {x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ}
  (hx : ↑x ∈ L.toIntermediateField)
  (hgx :
    ↑(((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) g) x) ∈
      L.toIntermediateField),
  Langlands.GaloisCohomology.levelUnit
      (((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) g) x) hgx =
    ((Langlands.GaloisCohomology.galUnitsHom K ↥L.toIntermediateField) (Langlands.GaloisCohomology.levelRestrict S L g))
      (Langlands.GaloisCohomology.levelUnit x hx)
@Langlands.GaloisCohomology.mem_level_galUnitsHom : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) {x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ},
  ↑x ∈ L.toIntermediateField →
    ↑(((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) g) x) ∈
      L.toIntermediateField
@Langlands.GaloisCohomology.exists_level_mem : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [IsGalois K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (x : ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
  ∃ (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)), x ∈ L.toIntermediateField
@Langlands.GaloisCohomology.levelRestrict_localizationHom : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  (h :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)),
  Langlands.GaloisCohomology.levelRestrict S L ((Langlands.Galois.localizationHom ι S v) h) =
    (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (Langlands.GaloisCohomology.levelEmbedding S ι v L.toIntermediateField))
      h
@Langlands.GaloisCohomology.sOrder_localizationHom : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀
      (h :
        Gal(AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
              v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (y : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ),
      Langlands.GaloisCohomology.sOrder S ι v
          (((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
              ((Langlands.Galois.localizationHom ι S v) h))
            y) =
        Langlands.GaloisCohomology.sOrder S ι v y
@Langlands.GaloisCohomology.sOrder_galUnitsHom_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
      {x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ} (hx : ↑x ∈ L.toIntermediateField)
      (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
      Langlands.GaloisCohomology.sOrder S ι v
          (((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) g) x) =
        Langlands.GaloisCohomology.placeExponent v
          (Langlands.GaloisCohomology.levelEmbedding S ι v L.toIntermediateField)
          (((Langlands.GaloisCohomology.galUnitsHom K ↥L.toIntermediateField)
              (Langlands.GaloisCohomology.levelRestrict S L g))
            (Langlands.GaloisCohomology.levelUnit x hx))
@Langlands.GaloisCohomology.outsideLocalizationHom : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S }) →
                  Gal(AlgebraicClosure
                        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
                          ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) →ₜ*
                    Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S
@Langlands.GaloisCohomology.sDivisorModule : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
@Langlands.GaloisCohomology.unitsDivisorFun : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ →
                  { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S } →
                    Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ULift.{u_1, 0} ℤ
@Langlands.GaloisCohomology.unitsDivisorFun_mem : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ),
  Langlands.GaloisCohomology.unitsDivisorFun S ι x ∈
    Langlands.GaloisCohomology.divisorFunctions (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
      (ULift.{u_1, 0} ℤ)
@Langlands.GaloisCohomology.unitsDivisor : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                Additive (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ →+
                  ↥(Langlands.GaloisCohomology.divisorFunctions (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                      (ULift.{u_1, 0} ℤ))
@Langlands.GaloisCohomology.unitsToSDivisor : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S) ⟶
                  Langlands.GaloisCohomology.sDivisorModule S ι
@Langlands.GaloisCohomology.unitsToSDivisor_hom_apply : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (x : Additive (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ)
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
  ↑((Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) x) v g =
    {
      down :=
        Langlands.GaloisCohomology.sOrder S ι (↑v)
          (((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) g)
            (Additive.toMul x)) }
@Langlands.GaloisCohomology.unitsToSDivisor_eq_zero_iff : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ),
  (Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) (Additive.ofMul x) = 0 ↔
    x ∈ Langlands.GaloisCohomology.maximalSUnits K Ω S
```

## Literature

- page reference to be added.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BrauerDivisor.lean` (lines 19–129) and `BrauerDivisorPlaces.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source's
`ordEmb`, `unitsDivFun`, `unitsDiv`, `gsDiv` are `sOrder`, `unitsDivisorFun`, `unitsToSDivisor`,
`sDivisorModule`; finite levels are intermediate fields of `K_S`, places of a level come from
`placeOfAlgHom` of the Library.
