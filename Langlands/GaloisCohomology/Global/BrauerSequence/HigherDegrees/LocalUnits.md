# The units of an unramified completion are cohomologically trivial

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/LocalUnits.lean`, namespace
`Langlands.GaloisCohomology`.

**Cyclic groups.** For a finite cyclic group `G` and a representation `A`:
`isZero_groupCohomology_odd`: `Hⁿ(G, A) = 0` for odd `n` if `H¹(G, A) = 0`;
`isZero_groupCohomology_even`: `Hⁿ(G, A) = 0` for even `n ≠ 0` if `H²(G, A) = 0`;
`isZero_groupCohomology_succ_of_isCyclic`: if `H¹` and `H²` vanish, so does `Hⁿ⁺¹` for every `n`.

**Completions.** Let `E / F` be a finite Galois extension of number fields and `w | v` finite places.
`subsingleton_relativeCohomology_one_adicCompletion`: `H¹(Gal(E_w/F_v), E_wˣ) = 0`;
`finite_relativeCohomology_two_adicCompletion`: `H²(Gal(E_w/F_v), E_wˣ)` is finite of order
`[E_w : F_v]` (both from the Library's local class formation `localRelativeClassFormation`). If `w` is
unramified over `v`: `isZero_H1_localUnits`, `isZero_H2_localUnits_of_ramificationIdx`,
`isZero_groupCohomology_localUnits`: `Hⁿ⁺¹(Gal(E_w/F_v), U_w) = 0` for every `n`, where `U_w` are the
valuation units; `isZero_groupCohomology_coindLocalUnits`: the same for the module `Coind(U_w)` of
`Gal(E/F)` coinduced along `decompositionHom v w`.

## Complete types

```lean
@Langlands.GaloisCohomology.isZero_groupCohomology_odd : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [Finite G] [IsCyclic G] (A : Rep.{u_1, u_1, u_1} k G),
  CategoryTheory.Limits.IsZero (groupCohomology A 1) →
    ∀ (n : ℕ), Odd n → CategoryTheory.Limits.IsZero (groupCohomology A n)
@Langlands.GaloisCohomology.isZero_groupCohomology_even : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [Finite G] [IsCyclic G] (A : Rep.{u_1, u_1, u_1} k G),
  CategoryTheory.Limits.IsZero (groupCohomology A 2) →
    ∀ (n : ℕ) [NeZero n], Even n → CategoryTheory.Limits.IsZero (groupCohomology A n)
@Langlands.GaloisCohomology.isZero_groupCohomology_succ_of_isCyclic : ∀ {k G : Type u_1} [inst : CommRing k]
  [inst_1 : Group G] [Finite G] [IsCyclic G] (A : Rep.{u_1, u_1, u_1} k G),
  CategoryTheory.Limits.IsZero (groupCohomology A 1) →
    CategoryTheory.Limits.IsZero (groupCohomology A 2) →
      ∀ (n : ℕ), CategoryTheory.Limits.IsZero (groupCohomology A (n + 1))
@Langlands.GaloisCohomology.subsingleton_relativeCohomology_one_adicCompletion : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal],
  Subsingleton
    ↑(Langlands.ClassFieldTheory.Local.relativeCohomology (Langlands.Global.CompletionPadic.padicField v).Carrier
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) 1)
@Langlands.GaloisCohomology.finite_relativeCohomology_two_adicCompletion : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal],
  Finite
      ↑(Langlands.ClassFieldTheory.Local.relativeCohomology (Langlands.Global.CompletionPadic.padicField v).Carrier
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) 2) ∧
    Nat.card
        ↑(Langlands.ClassFieldTheory.Local.relativeCohomology (Langlands.Global.CompletionPadic.padicField v).Carrier
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) 2) =
      Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)
@Langlands.GaloisCohomology.isZero_H1_localUnits : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal],
  w.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 →
    CategoryTheory.Limits.IsZero (groupCohomology (Langlands.ClassFieldTheory.Global.localUnitsRepresentation v w) 1)
@Langlands.GaloisCohomology.isZero_H2_localUnits_of_ramificationIdx : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal],
  w.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 →
    CategoryTheory.Limits.IsZero (groupCohomology (Langlands.ClassFieldTheory.Global.localUnitsRepresentation v w) 2)
@Langlands.GaloisCohomology.isZero_groupCohomology_localUnits : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal],
  w.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 →
    ∀ (n : ℕ),
      CategoryTheory.Limits.IsZero
        (groupCohomology (Langlands.ClassFieldTheory.Global.localUnitsRepresentation v w) (n + 1))
@Langlands.GaloisCohomology.isZero_groupCohomology_coindLocalUnits : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal],
  w.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 →
    ∀ (n : ℕ),
      CategoryTheory.Limits.IsZero
        (groupCohomology
          (Rep.coind.{u_1, u_1, u_1, u_1} (Langlands.ClassFieldTheory.Global.FundamentalClass.decompositionHom v w)
            (Langlands.ClassFieldTheory.Global.localUnitsRepresentation v w))
          (n + 1))
```

## Outline of the proofs

Periodicity is Mathlib's `Rep.FiniteCyclicGroup.groupCohomologyIsoOdd` and `groupCohomologyIsoEven`,
applied with the commutative group structure of a cyclic group. In degree one, a uniformizer of `F_v`
fixed by `Gal(E_w/F_v)` gives the Library's retraction `unitsRetraction` of `U_w → E_wˣ`, so
`H¹(U_w)` embeds into `H¹(E_wˣ) = 0`. Degree two is the Library's `isZero_H2_localUnits`, whose
hypothesis `#H²(Gal(E_w/F_v), E_wˣ) ≤ [E_w : F_v]` is `relativeH2_card` of the local invariant family.
`Gal(E_w/F_v)` is cyclic by the Library's `isCyclic_localGal`. The coinduced module is treated by
Shapiro's lemma (`Shapiro.shapiroIsoOf`).

## Declarations

`isZero_groupCohomology_odd`, `isZero_groupCohomology_even`, `isZero_groupCohomology_succ_of_isCyclic`, `subsingleton_relativeCohomology_one_adicCompletion`, `finite_relativeCohomology_two_adicCompletion`, `isZero_H1_localUnits`, `isZero_H2_localUnits_of_ramificationIdx`, `isZero_groupCohomology_localUnits`, `isZero_groupCohomology_coindLocalUnits`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J.-P. Serre, *Local Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VI, §1.2, Proposition 1, p. 131 (`H^q(G, U_n) = 0` for an
  unramified extension, all `q`).
