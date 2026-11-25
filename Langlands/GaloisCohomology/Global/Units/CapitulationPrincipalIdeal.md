# The divisor class group of `K_S` prime to `S` is trivial: capitulation at finite levels

`Langlands/GaloisCohomology/Global/Units/CapitulationPrincipalIdeal.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure of `K` (in the statements: `[IsGalois K Ω]
[IsSepClosed Ω]`), `S` any set of finite places of `K`, `K_S ⊆ Ω` the maximal extension unramified
outside `S` (ramification at the real places allowed), `G_S = Gal(K_S/K)`, `𝒪_Sˣ` the `S`-units of
`K_S` and `ι : PlaceEmbeddings K Ω`. The divisors of `K_S` prime to `S` form the `G_S`-module
`D = sDivisorModule S ι` of the module `Langlands.GaloisCohomology.Global.Units.DivisorMap`: a divisor
is a function `f(v, g)` (`v ∉ S`, `g ∈ G_S`), the multiplicity at the place `g⁻¹ w_v` above `v`
(`w_v` given by `ι`), with finite support in `v`, locally constant in `g` and invariant under the
decomposition group `Z_v` on the left. The divisor of a unit `y` of `K_S` is
`unitsToSDivisor y = ((v, g) ↦ sOrder v (g y))`, where `sOrder` is the exponent of the normalized
valuation (the order with the opposite sign).

The finite levels are the finite Galois subextensions `L` of `K_S / K`
(`FiniteGaloisIntermediateField K K_S`), with fixing group `U_L ⊆ G_S`. The divisors of `L` prime to
`S` are the divisors of `K_S` fixed by `U_L`; the place of `L` given by `ι` above `v ∉ S` is the
indicator `zuInd v U_L` of the double coset `Z_v U_L` at `v` (as in the module
`Langlands.GaloisCohomology.Global.Units.Capitulation`), and the other places of `L` above `v` are its
translates.

**Theorem** (`exists_level_forall_unitsToSDivisor_eq`, capitulation at finite levels). For every finite
level `L` there is a finite level `L' ⊇ L` such that every divisor of `L` prime to `S` is the divisor
of a unit of `K_S` lying in `L'`: every `S`-ideal of `L` becomes principal in `L'`.

Two finer forms: every place `W` of `L` (above `S` or not) becomes principal in `L'`, in the form
`x^h = placeUnit W · y` with `x ∈ L'`, `h` the class number of `L`, `placeUnit W` the generator of
`W^h` and `y` an `S`-unit of `K_S` (`exists_level_forall_pow_classNumber_eq`); and the place of `L`
given by `ι` above `v ∉ S` is the divisor of a unit lying in `L'`
(`exists_level_forall_sOrder_eq_single`).

**Consequences**, for every `S` and with no prime `ℓ`:

1. (`unitsToSDivisor_surjective`) The divisor map `K_Sˣ → D` is onto: the divisor class group of `K_S`
   prime to `S` is trivial.
2. (`isCapitulating_of_mem_divisorFunctions`) Every divisor of `K_S` prime to `S` is capitulating in
   the sense of `IsCapitulating S ι ℓ` of the module `Capitulation`, for every `ℓ : ℕ`, with `N = 1`
   (for `ℓ = 0` this says exactly that the divisor is principal). The module `Capitulation` proves
   this for a prime `ℓ` with the places above `ℓ` in `S`, with `N` prime to `ℓ`.
3. (`sUnitsDivisorSequence_shortExact`) `0 → 𝒪_Sˣ → K_Sˣ → D → 0` (`sUnitsDivisorSequence`: the
   inclusion `sUnitsToUnits` and `unitsToSDivisor`) is a short exact sequence of smooth `G_S`-modules.
4. (`isZero_sDivisorClassModule`, `sPrincipalDivisors_eq_top`) The divisor class module
   `sDivisorClassModule S ι` of the module `Langlands.GaloisCohomology.Global.Units.DivisorSequence` is
   zero, and `K_Sˣ/𝒪_Sˣ → D` is an isomorphism (`isIso_unitsModSUnitsToSDivisor`); the sequence
   `sDivisorSequence` of that module is `0 → K_Sˣ/𝒪_Sˣ ≅ D → 0 → 0`.
5. (`cohomologyOneSUnitsToSPicard_surjective_of_surjective`) The surjectivity of the divisor map of
   `K_S` gives that of `H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)` of the module
   `Langlands.GaloisCohomology.Global.Units.Picard`: with 1, this is `H¹(G_S, 𝒪_Sˣ) ≅ Pic(𝒪_S)`
   (NSW (8.3.11) (ii)), proved also, directly at the level of `K`, by
   `cohomologyOneSUnitsToSPicard_surjective` of the module
   `Langlands.GaloisCohomology.Global.Units.PicardCapitulation`.

In NSW the statement behind these is `lim Cl_S(K) = 0` over the finite subextensions `K` of `k_S`
(proof of (8.3.6) (i)), on which the class formation `(G_S, C_S)` of (8.3.9) rests; Milne, ADT, I,
Proposition 4.3 states it as `lim Id_{F,S} = 0`. Both prove it by the principal ideal theorem.

The file imports the NYLL library (the copy under `Nyll/`) through
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`, and so does every file that imports it; such
a file inherits NYLL's global instances and `simp` lemmas (described on the page of that module). This
file declares three instances, the smoothness of the terms of `sUnitsDivisorSequence`, and no `simp`
lemma.

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.exists_algHom_forall_mem_maximalUnramifiedOutside : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {L : Type u_2} [inst_6 : Field L]
  [NumberField L] [inst_8 : Algebra K L] [FiniteDimensional K L] [inst_10 : Algebra L Ω] [IsScalarTower K L Ω],
  (∀ v ∉ S, Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) v.asIdeal) →
    ∀ (H : Type u_3) [inst_12 : Field H] [NumberField H] [inst_14 : Algebra L H] [FiniteDimensional L H],
      (∀ w ∉ Langlands.Galois.finitePlacesAbove L S, Algebra.IsUnramifiedIn (NumberField.RingOfIntegers H) w.asIdeal) →
        ∃ φ, ∀ (z : H), φ z ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S

@Langlands.GaloisCohomology.nonempty_algHom_maximalUnramifiedOutside_of_le : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : IntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) [FiniteDimensional K ↥L] (H : Type u_2)
  [inst_7 : Field H] [NumberField H] [inst_9 : Algebra (↥L) H] [FiniteDimensional (↥L) H],
  (∀ w ∉ Langlands.Galois.finitePlacesAbove (↥L) S, Algebra.IsUnramifiedIn (NumberField.RingOfIntegers H) w.asIdeal) →
    Nonempty (H →ₐ[↥L] ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))

@Langlands.GaloisCohomology.exists_level_forall_pow_classNumber_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
  ∃ L',
    L ≤ L' ∧
      ∀ (W : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.toIntermediateField)),
        ∃ x,
          ↑x ∈ L'.toIntermediateField ∧
            ∃ y ∈ Langlands.GaloisCohomology.maximalSUnits K Ω S,
              x ^ NumberField.classNumber ↥L.toIntermediateField =
                (Units.map ↑L.val) (Langlands.GaloisCohomology.placeUnit W) * y

@Langlands.GaloisCohomology.sOrder_zpow : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ (y : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) (m : ℤ),
      Langlands.GaloisCohomology.sOrder S ι v (y ^ m) = m * Langlands.GaloisCohomology.sOrder S ι v y

@Langlands.GaloisCohomology.sOrder_inv : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ (y : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ),
      Langlands.GaloisCohomology.sOrder S ι v y⁻¹ = -Langlands.GaloisCohomology.sOrder S ι v y

@Langlands.GaloisCohomology.sOrder_galUnitsHom_placeUnit : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) (v v' : { v // v ∉ S })
  (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
  Langlands.GaloisCohomology.sOrder S ι (↑v')
      (((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) g)
        ((Units.map ↑L.val)
          (Langlands.GaloisCohomology.placeUnit
            ↑(Langlands.Galois.placeOfAlgHom
                (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) L.toIntermediateField))))) =
    -↑(NumberField.classNumber ↥L.toIntermediateField) *
      Pi.single v (Langlands.GaloisCohomology.zuInd S ι v L.fixingSubgroup) v' g

@Langlands.GaloisCohomology.exists_level_forall_sOrder_eq_single : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
  ∃ L',
    L ≤ L' ∧
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω) (v : { v // v ∉ S }),
        ∃ y,
          ↑y ∈ L'.toIntermediateField ∧
            ∀ (v' : { v // v ∉ S }) (g : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
              Langlands.GaloisCohomology.sOrder S ι (↑v')
                  (((Langlands.GaloisCohomology.galUnitsHom K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) g)
                    y) =
                Pi.single v (Langlands.GaloisCohomology.zuInd S ι v L.fixingSubgroup) v' g

@Langlands.GaloisCohomology.IsPrincipalIn : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S) →
                  ({ v // v ∉ S } → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ) → Prop

@Langlands.GaloisCohomology.isPrincipalIn_zero : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {L' : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)},
  Langlands.GaloisCohomology.IsPrincipalIn S ι L' 0

@Langlands.GaloisCohomology.IsPrincipalIn.add : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {L' : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
  {f g : { v // v ∉ S } → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ},
  Langlands.GaloisCohomology.IsPrincipalIn S ι L' f →
    Langlands.GaloisCohomology.IsPrincipalIn S ι L' g → Langlands.GaloisCohomology.IsPrincipalIn S ι L' (f + g)

@Langlands.GaloisCohomology.IsPrincipalIn.zsmul : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {L' : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
  {f : { v // v ∉ S } → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ},
  Langlands.GaloisCohomology.IsPrincipalIn S ι L' f → ∀ (c : ℤ), Langlands.GaloisCohomology.IsPrincipalIn S ι L' (c • f)

@Langlands.GaloisCohomology.isPrincipalIn_sum : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {L' : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)} {J : Type u_2}
  (T : Finset J) (f : J → { v // v ∉ S } → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ),
  (∀ i ∈ T, Langlands.GaloisCohomology.IsPrincipalIn S ι L' (f i)) →
    Langlands.GaloisCohomology.IsPrincipalIn S ι L' (∑ i ∈ T, f i)

@Langlands.GaloisCohomology.IsPrincipalIn.translate : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {L' : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
  {f : { v // v ∉ S } → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ},
  Langlands.GaloisCohomology.IsPrincipalIn S ι L' f →
    ∀ (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
      Langlands.GaloisCohomology.IsPrincipalIn S ι L' fun v x => f v (x * g)

@Langlands.GaloisCohomology.IsPrincipalIn.isCapitulating : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {L' : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)}
  {f : { v // v ∉ S } → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ},
  Langlands.GaloisCohomology.IsPrincipalIn S ι L' f → ∀ (ℓ : ℕ), Langlands.GaloisCohomology.IsCapitulating S ι ℓ f

@Langlands.GaloisCohomology.isPrincipalIn_single_of_base : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {L' : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)} (v : { v // v ∉ S })
  (U : Subgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [hUn : U.Normal],
  IsOpen ↑U →
    Langlands.GaloisCohomology.IsPrincipalIn S ι L' (Pi.single v (Langlands.GaloisCohomology.zuInd S ι v U)) →
      ∀ (φ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ),
        (∀ (x u : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S), u ∈ U → φ (x * u) = φ x) →
          (∀ z ∈ Langlands.GaloisCohomology.decompositionSubgroup S ι ↑v,
              ∀ (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S), φ (z * x) = φ x) →
            Langlands.GaloisCohomology.IsPrincipalIn S ι L' (Pi.single v φ)

@Langlands.GaloisCohomology.exists_level_forall_unitsToSDivisor_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (L : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
  ∃ L',
    L ≤ L' ∧
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω) (f : ↑(Langlands.GaloisCohomology.sDivisorModule S ι)),
        (∀ u ∈ L.fixingSubgroup, ((Langlands.GaloisCohomology.sDivisorModule S ι).ρ u) f = f) →
          ∃ y,
            ↑y ∈ L'.toIntermediateField ∧
              (Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) (Additive.ofMul y) = f

@Langlands.GaloisCohomology.exists_level_forall_ρ_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (f : ↑(Langlands.GaloisCohomology.sDivisorModule S ι)),
  ∃ L, ∀ u ∈ L.fixingSubgroup, ((Langlands.GaloisCohomology.sDivisorModule S ι).ρ u) f = f

@Langlands.GaloisCohomology.unitsToSDivisor_surjective : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Function.Surjective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι))

@Langlands.GaloisCohomology.isCapitulating_of_mem_divisorFunctions : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ℓ : ℕ)
  (F : { v // v ∉ S } → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S → ℤ),
  (fun v g => { down := F v g }) ∈
      Langlands.GaloisCohomology.divisorFunctions (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
        (ULift.{u_1, 0} ℤ) →
    Langlands.GaloisCohomology.IsCapitulating S ι ℓ F

@Langlands.GaloisCohomology.sUnitsDivisorSequence : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Langlands.Galois.PlaceEmbeddings K Ω →
                CategoryTheory.ShortComplex
                  (Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))

@Langlands.GaloisCohomology.isSmoothRep_sUnitsDivisorSequence_X₁ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.sUnitsDivisorSequence S ι).X₁

@Langlands.GaloisCohomology.isSmoothRep_sUnitsDivisorSequence_X₂ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.sUnitsDivisorSequence S ι).X₂

@Langlands.GaloisCohomology.isSmoothRep_sUnitsDivisorSequence_X₃ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.sUnitsDivisorSequence S ι).X₃

@Langlands.GaloisCohomology.sUnitsDivisorSequence_shortExact : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [IsSepClosed Ω],
  (Langlands.GaloisCohomology.sUnitsDivisorSequence S ι).ShortExact

@Langlands.GaloisCohomology.sPrincipalDivisors_eq_top : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [IsSepClosed Ω], Langlands.GaloisCohomology.sPrincipalDivisors S ι = ⊤

@Langlands.GaloisCohomology.isZero_sDivisorClassModule : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [IsSepClosed Ω],
  CategoryTheory.Limits.IsZero (Langlands.GaloisCohomology.sDivisorClassModule S ι)

@Langlands.GaloisCohomology.isIso_unitsModSUnitsToSDivisor : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [IsSepClosed Ω],
  CategoryTheory.IsIso (Langlands.GaloisCohomology.unitsModSUnitsToSDivisor S ι)

@Langlands.GaloisCohomology.ordAbove_eq_neg_sOrder : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)},
  v ∉ S →
    ∀ {x : (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ},
      Langlands.GaloisCohomology.IsSInvariant S x →
        Langlands.GaloisCohomology.ordAbove S v x = -Langlands.GaloisCohomology.sOrder S ι v x

@Langlands.GaloisCohomology.divAbove_surjective_of_surjective : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Function.Surjective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) →
    Function.Surjective ⇑(Langlands.GaloisCohomology.divAbove S)

@Langlands.GaloisCohomology.cohomologyOneSUnitsToSPicard_surjective_of_surjective : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Function.Surjective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.unitsToSDivisor S ι)) →
    Function.Surjective ⇑(Langlands.GaloisCohomology.cohomologyOneSUnitsToSPicard S)
```

## Outline of the proofs

*Embedding over a level.* Let `L ⊆ K_S` be finite over `K` and `H / L` finite with the places of `L`
outside the places above `S` unramified. Regard `Ω` as an `L`-algebra through `K_S`, choose an
`L`-embedding `φ : H → Ω` (`IsSepClosed.lift`) and regard `Ω` as an `H`-algebra through it. The image
`E = (⊥ : IntermediateField H Ω).restrictScalars L` is unramified over `L` outside the places above
`S` (`isUnramifiedOutside_restrictScalars_iff` over `L` with `isUnramifiedOutside_bot`); since `L / K`
is unramified outside `S` (`isUnramifiedIn_of_maximalUnramifiedOutside`), `E.restrictScalars K` is
unramified outside `S` (`isUnramifiedOutside_restrictScalars_iff` over `K`), so it lies in `K_S`
(`le_maximalUnramifiedOutside`) (`exists_algHom_forall_mem_maximalUnramifiedOutside`,
`nonempty_algHom_maximalUnramifiedOutside_of_le`).

*Principal ideal theorem in `K_S`.* Apply `exists_unramified_extension_forall_isPrincipal` to `L`: a
finite extension `H / L`, unramified at every finite place, in which every ideal of `𝓞 L` becomes
principal. Embed `H` into `K_S` over `L` and let `L'` be a finite Galois level containing the image
(`exists_finiteGaloisIntermediateField_le`); it contains `L`. For a place `W` of `L` let
`W^h = (a)` (`exists_pow_classNumber_eq_span`, `a` the element behind `placeUnit W`) and
`W 𝓞_H = (α)`; then `(α^h) = (a)`, so `α^h u = a` with `u ∈ (𝓞 H)ˣ`
(`Ideal.span_singleton_eq_span_singleton`). The image `x` of `α` lies in `L'`, and the image of `u`
is an `S`-unit of `K_S` because `u` and `u⁻¹` are integral over `ℤ`. This is the argument of
`exists_divAbove_eq_single` of the module `PicardCapitulation` with `L` in place of `K`.

*Divisors.* `sOrder` is additive (`sOrder_mul`, `sOrder_zpow`, `sOrder_inv`) and vanishes on
`S`-units (`sOrder_eq_zero_of_mem`). The divisor of `placeUnit W` for the place `W` of `ι` above `v`
is `-h` times the indicator of `Z_v U_L` at `v` (`sOrder_galUnitsHom_placeUnit`): its valuation is
`exp(-h)` at `W` and `1` at the other places of `L`
(`valuationOfNeZero_placeUnit`), and the place of `ι ∘ g` is `W` exactly when `v' = v` and
`g ∈ Z_v U_L` (`placeOfAlgHom_comp_eq_iff`, `mem_decompositionSubgroup_mul_iff`); this is the
computation of `isCapitulating_base` of the module `Capitulation`. Hence `h` times the divisor of `x`
is `-h` times that indicator, and `h ≠ 0` cancels: `x⁻¹` has divisor the place of `L`
(`exists_level_forall_sOrder_eq_single`).

*All divisors of `L`.* A function is principal in `L'` (`IsPrincipalIn S ι L'`) if it is the
divisor function of a unit of `K_S` lying in `L'`; this is stable under sums, integral multiples and
right translations (`L'` is Galois over `K`). A function at a place `v` that is left `Z_v`-invariant
and right `U_L`-invariant is an integral combination of right translates of the indicator of
`Z_v U_L`, by induction on the number of cosets of `U_L` on which it is nonzero
(`isPrincipalIn_single_of_base`, the argument of `isCapitulating_single_of_base` of the module
`Capitulation` for this predicate). A divisor is the finite sum of its components at the places of
its support (`eq_sum_single`), which gives `exists_level_forall_unitsToSDivisor_eq`.

*Consequences.* Every divisor is fixed by `U_L` for some level `L`: its stabilizer is open
(`IsSmoothRep.isOpen_stabilizer`), so it contains the fixing group of a finite subextension
(`krullTopology_mem_nhds_one_iff`), and of a finite Galois level containing it
(`exists_level_forall_ρ_eq`). Hence `unitsToSDivisor` is onto. The kernel of `unitsToSDivisor` is
`𝒪_Sˣ` (`unitsToSDivisor_eq_zero_iff`) and `sUnitsToUnits` is injective, which gives the short exact
sequence; the quotient of `D` by the principal divisors is zero (`Rep.isZero_iff`); and
`K_Sˣ/𝒪_Sˣ → D` is injective (`sDivisorSequence_shortExact`) and onto, hence an isomorphism in the
abelian category of representations.

*The check.* For an `S`-invariant unit `x` and `v ∉ S`, the order `ordAbove v x` of the module
`Langlands.GaloisCohomology.Global.Units.Divisor` is `-sOrder v x` (`ordAbove_eq_neg_sOrder`):
transport the place of `ι` of a level `L ∋ x` to the subfield `L.map K_S.val` of `Ω`
(`finitePlaceEquiv`, `finitePlaceEquiv_valuation`) and compare with `valuation_eq_exp_ordAbove`. For
`v ∉ S` take a unit `x` with divisor `-1` at every place above `v` and `0` elsewhere (a `G_S`-invariant
divisor, so `x` is `S`-invariant by `unitsToSDivisor_eq_zero_iff`); then `divAbove x` is the divisor
`v` of `K`, so `divAbove` is onto (`divAbove_surjective_of_surjective`), and so is
`cohomologyOneSUnitsToSPicard` (`cohomologyOneSUnitsToSPicard_apply`).

## Declarations

In order: `exists_algHom_forall_mem_maximalUnramifiedOutside`,
`nonempty_algHom_maximalUnramifiedOutside_of_le`, `exists_level_forall_pow_classNumber_eq`,
`sOrder_zpow`, `sOrder_inv`, `sOrder_galUnitsHom_placeUnit`, `exists_level_forall_sOrder_eq_single`,
`IsPrincipalIn`, `isPrincipalIn_zero`, `IsPrincipalIn.add`, `IsPrincipalIn.zsmul`,
`isPrincipalIn_sum`, `IsPrincipalIn.translate`, `IsPrincipalIn.isCapitulating`,
`isPrincipalIn_single_of_base`, `exists_level_forall_unitsToSDivisor_eq`, `exists_level_forall_ρ_eq`,
`unitsToSDivisor_surjective`, `isCapitulating_of_mem_divisorFunctions`, `sUnitsDivisorSequence`,
instances `isSmoothRep_sUnitsDivisorSequence_X₁`, `_X₂`, `_X₃`, `sUnitsDivisorSequence_shortExact`,
`sPrincipalDivisors_eq_top`, `isZero_sDivisorClassModule`, `isIso_unitsModSUnitsToSDivisor`,
`ordAbove_eq_neg_sOrder`, `divAbove_surjective_of_surjective`,
`cohomologyOneSUnitsToSPicard_surjective_of_surjective`.

## Source and licence

The proofs of `sOrder_galUnitsHom_placeUnit` and `isPrincipalIn_single_of_base` follow those of
`isCapitulating_base` and `isCapitulating_single_of_base` of the module
`Langlands.GaloisCohomology.Global.Units.Capitulation`, which are ported from the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BrauerDivisor.lean`
(lines 176–546). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The rest of the file is not from the
source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013), chapter VIII, §3: p. 452 (the conventions: `S` contains the archimedean
  primes, `k_S`, `𝒪_{K,S}`, the `S`-ideal class group `Cl_S(K)`); Proposition (8.3.5), p. 455
  (`0 → C_{K,S} → C_S(K) → Cl_S(K) → 0`); Proposition (8.3.6) and its proof, pp. 455–456
  (`lim Cl_S(K) = 0` over the finite subextensions `K` of `k_S`, "since every ideal in `𝒪_{K,S}`
  becomes a principal ideal in a suitable finite unramified Galois extension `L|K`", by the principal
  ideal theorem); Proposition (8.3.9), p. 457 (the class formation `(G_S, C_S)`); Proposition
  (8.3.11) (ii), p. 458 (`H¹(G_S, 𝒪_Sˣ) ≅ Cl_S(k)`). In the book `S` contains the archimedean primes
  and `k_S` is unramified outside `S`; the `S` of this file is a set of finite places and `K_S` may
  ramify at the real places, so it is the book's `k_{S ∪ S_∞}`, and the divisors prime to `S` of a
  finite level `L` modulo principal divisors form the book's `Cl_{S ∪ S_∞}(L)`.
- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322 (Springer 1999), chapter VI, §7: (7.5)
  Theorem (the principal ideal theorem) and (7.6) Theorem (the transfer `G/G' → G'/G''` is trivial),
  p. 410.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4: Lemma 4.1,
  p. 49 (`0 → C_{F,S} → C_F/U_{F,S} → Id_{F,S} → 0`), Proposition 4.3 and its proof, p. 50
  (`lim Id_{F,S} = 0` over the finite extensions `F` of `K` in `K_S`, by the principal ideal theorem).
