# The Kummer sequence of the `S`-units

`Langlands/GaloisCohomology/Global/Units/Kummer.lean`, namespace `Langlands.GaloisCohomology`.

For `n ≠ 0`, `sUnitsKummerSequence S E n` is the short complex `μ_n(E) → 𝒪_{E,S}ˣ → 𝒪_{E,S}ˣ` of
`Gal(E / F)`-modules (inclusion, then multiplication by `n`). For a Galois extension `Ω / F` with
`Ω` separably closed and `n` invertible outside `S`, the sequence for `E = K_S` is short exact over
`G_S` (`sUnitsKummerSequence_shortExact`): `n`-th roots of `S`-units of `K_S` are `S`-units of `K_S`
(`exists_pow_eq_of_mem_maximalSUnits`). Its long exact sequence, with
`H⁰(G_S, 𝒪_Sˣ) = 𝒪_{F,S}ˣ` and `H¹(G_S, 𝒪_Sˣ) ↪ Pic(𝒪_S)`, gives

`0 → 𝒪_{F,S}ˣ / n → H¹(G_S, μ_n) → Pic(𝒪_S)[n] → 0`:

- the Kummer map `kummerSUnitsHom : 𝒪_{F,S}ˣ → H¹(G_S, μ_n)` (the connecting map) vanishes exactly on
  `n`-th powers (`kummerSUnitsHom_eq_zero_iff`);
- the kernel of `kummerPicHom : H¹(G_S, μ_n) → H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)` is the image of the Kummer
  map (`kummerPicHom_eq_zero_iff`);
- the image of `kummerPicHom` is the `n`-torsion of `Pic(𝒪_S)` (`mem_range_kummerPicHom_iff`).

Finally the `S`-units of a field over a finite extension `L` of `F` for the places of `L` above `S`
are its `S`-units over `F` (`sUnitsOf_finitePlacesAbove_eq`).

## Complete types

```lean
@Langlands.GaloisCohomology.sUnitsKummerSequence : {F : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
        (E : Type u_1) →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              (n : ℕ) → [NeZero n] → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(E/F))

@Langlands.GaloisCohomology.sUnitsKummerSequence_shortExact : ∀ {F : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  {Ω : Type u_1} [inst_2 : Field Ω] [inst_3 : Algebra F Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) [IsGalois F Ω] [IsSepClosed Ω] (n : ℕ)
  [inst_6 : NeZero n],
  (∀ v ∉ S, ↑n ∉ v.asIdeal) →
    (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S))
        n).ShortExact

@Langlands.GaloisCohomology.kummerSUnitsHom : {F Ω : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra F Ω] →
          [inst_4 : IsGalois F Ω] →
            [IsSepClosed Ω] →
              (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
                (n : ℕ) →
                  [NeZero n] →
                    (∀ v ∉ S, ↑n ∉ v.asIdeal) →
                      Additive ↥(S.unit F) →+
                        ↑(Langlands.ProfiniteCohomology.cohomology
                            (Langlands.GaloisCohomology.rootsOfUnityModule F
                              (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S)) n)
                            1)

@Langlands.GaloisCohomology.kummerPicHom : {F Ω : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra F Ω] →
          [inst_4 : IsGalois F Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) →
              (n : ℕ) →
                [NeZero n] →
                  ↑(Langlands.ProfiniteCohomology.cohomology
                        (Langlands.GaloisCohomology.rootsOfUnityModule F
                          (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S)) n)
                        1) →+
                    Langlands.GaloisCohomology.SPicardGroup S

@Langlands.GaloisCohomology.kummerSUnitsHom_eq_zero_iff : ∀ {F Ω : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω] [inst_5 : IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (n : ℕ) [inst_6 : NeZero n]
  (hnS : ∀ v ∉ S, ↑n ∉ v.asIdeal) (a : Additive ↥(S.unit F)),
  (Langlands.GaloisCohomology.kummerSUnitsHom S n hnS) a = 0 ↔ ∃ (b : Additive ↥(S.unit F)), n • b = a

@Langlands.GaloisCohomology.kummerPicHom_eq_zero_iff : ∀ {F Ω : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω] [inst_5 : IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (n : ℕ) [inst_6 : NeZero n]
  (hnS : ∀ v ∉ S, ↑n ∉ v.asIdeal)
  (y :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.rootsOfUnityModule F (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S)) n) 1)),
  (Langlands.GaloisCohomology.kummerPicHom S n) y = 0 ↔
    ∃ (a : Additive ↥(S.unit F)), (Langlands.GaloisCohomology.kummerSUnitsHom S n hnS) a = y

@Langlands.GaloisCohomology.mem_range_kummerPicHom_iff : ∀ {F Ω : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field Ω] [inst_3 : Algebra F Ω] [inst_4 : IsGalois F Ω] [IsSepClosed Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (n : ℕ) [inst_6 : NeZero n],
  (∀ v ∉ S, ↑n ∉ v.asIdeal) →
    ∀ (c : Langlands.GaloisCohomology.SPicardGroup S),
      (∃ (y :
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.rootsOfUnityModule F (↥(Langlands.Galois.maximalUnramifiedOutside F Ω S)) n)
              1)),
          (Langlands.GaloisCohomology.kummerPicHom S n) y = c) ↔
        n • c = 0

@Langlands.GaloisCohomology.sUnitsOf_finitePlacesAbove_eq : ∀ {F L E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Field E] [inst_5 : Algebra F L]
  [inst_6 : Algebra F E] [inst_7 : Algebra L E] [IsScalarTower F L E]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))),
  Langlands.GaloisCohomology.sUnitsOf (Langlands.Galois.finitePlacesAbove L S) E =
    Langlands.GaloisCohomology.sUnitsOf S E
```

## Outline of the proofs

Exactness on the left and in the middle of the Kummer sequence is the definition of `μ_n`; onto on
the right is `exists_pow_eq_of_mem_maximalSUnits`. The three statements on `H¹(G_S, μ_n)` are the
exactness of the long exact cohomology sequence (`cohomology_exact₁`, `δ_zeroIso_inv_eq_zero_iff`
of the foundations and of `Field/KummerSequence.lean`) combined with the injectivity of
`cohomologyOneSUnitsToSPicard` and its surjectivity onto `n`-torsion (`Picard.lean`);
multiplication by `n` acts on `H¹` as `n` (`cohomologyMap_nsmul_id_apply`).

## Declarations

`sUnitsKummerSequence`, `sUnitsKummerSequence_g`, `sUnitsKummerSequence_shortExact`,
`isSmoothRep_sUnitsKummerSequence_X₁`, `_X₂`, `_X₃`, `invariantsFunctor_map_nsmul_apply`,
`kummerSUnitsHom`, `kummerPicHom`, `kummerSUnitsHom_eq_zero_iff`, `kummerPicHom_eq_zero_iff`,
`mem_range_kummerPicHom_iff`, `isIntegral_integer_iff_finitePlacesAbove`,
`sUnitsOf_finitePlacesAbove_eq`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files (under
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`) `SUnitsDefs.lean` (lines 120–133),
`SUnits.lean` (lines 388–418) and `SInvariantToInvariantsEqZeroIff.lean` (sections `KummerPic` and
`BaseChange`, lines 239–374). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the
foundations' names (`coeffMap`, `zeroIso`, `rootsOfUnityModule`, `IsSmoothRep`);
`isIntegral_integer_iff_placesOver`, `sUnitsOf_placesOver_eq` are
`isIntegral_integer_iff_finitePlacesAbove`, `sUnitsOf_finitePlacesAbove_eq`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): chapter VIII, §3, Proposition (8.3.4), p. 453 (the exact sequence of
  `G_S`-modules `0 → μ_n → 𝒪_Sˣ → 𝒪_Sˣ → 0` for `n` invertible outside `S`).
