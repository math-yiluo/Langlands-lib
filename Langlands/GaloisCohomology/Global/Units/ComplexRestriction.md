# Restriction of Brauer classes to totally complex extensions inside `K_S`

`Langlands/GaloisCohomology/Global/Units/ComplexRestriction.lean`, namespace `Langlands.GaloisCohomology`.

- `brauerRestriction_eq_zero_of_isComplex`: a class `x ∈ H²(Gal(Ω/K), Ωˣ)` killed by `m` dies in every
  finite extension `E ⊆ Ω` of `K` without real places whose local degrees above the finite places
  where `x` is nonzero are multiples of `m`: the case of `brauerRestriction_eq_zero'`
  (`Langlands.GaloisCohomology.Global.BrauerSequence.Restriction`) in which `E` has no real place, so
  that its condition on the real localizations of `x` is empty.
- `exists_isComplex_le_maximalUnramifiedOutside`: for a prime `ℓ` with the places above `ℓ` in `S`,
  a finite set `T` of finite places and `a`, there is a finite extension `E ⊆ K_S` of `K` without real
  places whose local degrees above `T` are multiples of `ℓ^a`: the image of the field `xiField K ℓ k`
  of `Langlands.Global.Arithmetic.CyclotomicSplitting` (a subfield of `K(μ_{ℓ^{k+3}})`, which lies in
  `K_S`).

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.brauerRestriction_eq_zero_of_isComplex : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : FiniteDimensional K ↥E],
  (∀ (u : NumberField.InfinitePlace ↥E), u.IsComplex) →
    ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)) (m : ℕ),
      m • x = 0 →
        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
            (Langlands.GaloisCohomology.brauerLocalization ι v 2) x ≠ 0 →
              ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E))
                [inst_6 : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree E v w) →
          (Langlands.GaloisCohomology.brauerRestriction E) x = 0
@Langlands.GaloisCohomology.exists_isComplex_le_maximalUnramifiedOutside : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (a : ℕ),
        ∃ (E : IntermediateField K Ω) (x : FiniteDimensional K ↥E),
          E ≤ Langlands.Galois.maximalUnramifiedOutside K Ω S ∧
            (∀ (u : NumberField.InfinitePlace ↥E), u.IsComplex) ∧
              ∀ v ∈ T,
                ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E))
                  [inst_5 : w.asIdeal.LiesOver v.asIdeal], ℓ ^ a ∣ Langlands.GaloisCohomology.localDegree E v w
```

## Literature

- page reference to be added.

## Source and licence

New. `brauerRestriction_eq_zero_of_isComplex` is a case of the Library's
`brauerRestriction_eq_zero'` (`Langlands.GaloisCohomology.Global.BrauerSequence.Restriction`); no text
of the source is used.
