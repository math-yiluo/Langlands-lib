# `H³(Gal(Ω/K), Ωˣ) = 0`

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/DegreeThree.lean`, namespace
`Langlands.GaloisCohomology`.

Let `K` be a number field and `Ω` a separable closure.

* `nonempty_heightOneSpectrum`: a number field has a finite place.
* `exists_le_localDegreesDvd_of_finset`, `exists_le_localDegreesDvd`: over a finite Galois level
  `E ⊆ Ω` there is a larger finite Galois level `L` whose local degrees above every place of a finite
  set `T` (or above one place `v`) are divisible by a given `m ≠ 0`; `exists_le_dvd_finrank`: one with
  `[E : K] ∣ [L : E]`.
* `unitsInflation_three_eq_zero`: a class of `H³(Gal(E/K), Eˣ)` at a finite Galois level inflates to
  zero in `H³(Gal(Ω/K), Ωˣ)`.
* `subsingleton_cohomology_three_unitsModule`: **`H³(Gal(Ω/K), Ωˣ) = 0`**.

## Complete types

```lean
Langlands.GaloisCohomology.nonempty_heightOneSpectrum : ∀ (K : Type u_1) [inst : Field K] [NumberField K],
  Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
@Langlands.GaloisCohomology.exists_le_localDegreesDvd_of_finset : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω] (E : IntermediateField K Ω)
  [FiniteDimensional K ↥E] [IsGalois K ↥E]
  (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (m : ℕ),
  m ≠ 0 →
    ∃ (L : IntermediateField K Ω) (x : FiniteDimensional K ↥L),
      IsGalois K ↥L ∧
        E ≤ L ∧
          ∀ v ∈ T,
            ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
              [inst_7 : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree L v w
@Langlands.GaloisCohomology.exists_le_localDegreesDvd : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω] (E : IntermediateField K Ω) [FiniteDimensional K ↥E]
  [IsGalois K ↥E] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (m : ℕ),
  m ≠ 0 →
    ∃ (L : IntermediateField K Ω) (x : FiniteDimensional K ↥L),
      IsGalois K ↥L ∧
        E ≤ L ∧
          ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
            [inst_7 : w.asIdeal.LiesOver v.asIdeal], m ∣ Langlands.GaloisCohomology.localDegree L v w
@Langlands.GaloisCohomology.exists_le_dvd_finrank : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω] (E : IntermediateField K Ω) [FiniteDimensional K ↥E]
  [IsGalois K ↥E],
  ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K ↥L),
    IsGalois K ↥L ∧ ∃ (h : E ≤ L), Module.finrank K ↥E ∣ Module.finrank ↥E ↥L
@Langlands.GaloisCohomology.unitsInflation_three_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω] (E : IntermediateField K Ω)
  [inst_5 : FiniteDimensional K ↥E] [inst_6 : IsGalois K ↥E]
  (a : ↑(groupCohomology (Langlands.GaloisCohomology.unitsModule K ↥E) 3)),
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E 3)) a = 0
@Langlands.GaloisCohomology.subsingleton_cohomology_three_unitsModule : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω],
  Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 3)
```

## Outline of the proofs

Levels: a cyclic layer with the prescribed local degrees (`exists_cyclic_layer`) composed with `E`;
local degrees grow in towers (`localDegreesDvd_of_le`) and divide the global degree
(`localDegree_dvd`). Every class of `H³(Gal(Ω/K), Ωˣ)` is inflated from a finite level `E`
(`exists_unitsInflation_eq`), `x = infl a`. Since `H³(Gal(E/K), J_E) = 0`, the long exact sequence of
`0 → Eˣ → J_E → C_E → 0` gives `a = δ c` with `c ∈ H²(Gal(E/K), C_E)`. At a level `L` with a finite
place of local degree divisible by `[E : K]`, the inflation of `c` is the image of an idèle class
(`relativeIdeleClassInflation_mem_range`), so the inflation of `a` to `L` is `δ` of an image, which is
zero (`δ_comp_relativeInflation`, exactness); and `x` is the inflation of that class
(`unitsInflationOfLE_comp_unitsInflation`, `unitsInflationOfLE_eq_relativeInflation`). This is Tate's
argument: at a finite level `H³(L/K, Lˣ)` is cyclic of order `n / n₀` and is killed by inflation to a
level whose local degrees are large.

## Declarations

`nonempty_heightOneSpectrum`, `exists_le_localDegreesDvd_of_finset`, `exists_le_localDegreesDvd`, `exists_le_dvd_finrank`, `unitsInflation_three_eq_zero`, `subsingleton_cohomology_three_unitsModule`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. It
replaces the source's `subsingleton_cohomology_three_unitsLimitRep` (`GlobalClassFormation.lean`),
proved there through limit modules of idèles and idèle classes and the source's class formation, by a
proof at finite levels from the Library's class field theory.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §11.4, pp. 198–199 ("Case `r = 3`": `H³(G, Lˣ)` is
  cyclic of order `n/n₀`, killed by inflation to a larger `L'`, so `H³(K̄/K, K̄ˣ) = 0`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013), Chapter VIII, §1, Proposition (8.1.20) and its proof, p. 439.
