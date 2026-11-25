# Inflation kills cohomology of degree `≥ 3` of idèle classes and of local units

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/HighDegreeInflation.lean`, namespace
`Langlands.GaloisCohomology`.

* `integralInflationIdentity`: the identity of `ℤ` as a coefficient map of inflation.
* `exists_fundamentalClassFamily`: the Library's global fundamental classes, a family generating
  `H²(Gal(E/F), C_E)` and compatible with restriction and inflation
  (from `globalFundamentalClassStatement`).
* `relativeIdeleClassInflation_eq_zero_of_dvd`: **for number fields `F ⊆ E ⊆ L` with `E / F`,
  `L / F` Galois and `[E : F] ∣ [L : E]`, inflation `Hⁿ⁺²(Gal(E/F), C_E) → Hⁿ⁺²(Gal(L/F), C_L)` is zero
  for `n ≥ 1`.**
* `relativeInflation_adicCompletion_eq_zero_of_dvd`: the same for the units of the completions at
  finite places `q | w | v` with `[E_w : F_v] ∣ [L_q : E_w]`.

## Complete types

```lean
@Langlands.GaloisCohomology.integralInflationIdentity : {F E L : Type u_1} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Field L] →
        [inst_3 : Algebra F E] →
          [inst_4 : Algebra F L] →
            [inst_5 : Algebra E L] →
              [inst_6 : IsScalarTower F E L] →
                [inst_7 : IsGalois F E] →
                  Rep.res (AlgEquiv.restrictNormalHom E)
                      (Rep.trivial Langlands.Tate.IntegralScalar Gal(E/F) Langlands.Tate.IntegralScalar) ⟶
                    Rep.trivial Langlands.Tate.IntegralScalar Gal(L/F) Langlands.Tate.IntegralScalar
Langlands.GaloisCohomology.exists_fundamentalClassFamily : ∃ (c :
  Langlands.ClassFieldTheory.Global.FundamentalClass.ClassFamily),
  Langlands.ClassFieldTheory.Global.FundamentalClass.Generates c ∧
    Langlands.ClassFieldTheory.Global.FundamentalClass.Restriction c ∧
      Langlands.ClassFieldTheory.Global.FundamentalClass.Inflation c
@Langlands.GaloisCohomology.relativeIdeleClassInflation_eq_zero_of_dvd : ∀ {F E L : Type u_1} [inst : Field F]
  [inst_1 : Field E] [inst_2 : Field L] [NumberField F] [inst_4 : NumberField E] [inst_5 : NumberField L]
  [inst_6 : Algebra F E] [inst_7 : Algebra F L] [inst_8 : Algebra E L] [inst_9 : IsScalarTower F E L]
  [inst_10 : IsGalois F E] [IsGalois F L],
  Module.finrank F E ∣ Module.finrank E L →
    ∀ (n : ℕ) [NeZero n] (x : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleClassCohomology F E (n + 2))),
      (CategoryTheory.ConcreteCategory.hom
            (Langlands.ClassFieldTheory.Global.relativeIdeleClassInflation F E L (n + 2)))
          x =
        0
@Langlands.GaloisCohomology.relativeInflation_adicCompletion_eq_zero_of_dvd : ∀ {F E L : Type u_1} [inst : Field F]
  [inst_1 : Field E] [inst_2 : Field L] [inst_3 : NumberField F] [inst_4 : NumberField E] [inst_5 : NumberField L]
  [inst_6 : Algebra F E] [inst_7 : Algebra F L] [inst_8 : Algebra E L] [inst_9 : IsScalarTower F E L]
  [inst_10 : IsGalois F E] [IsGalois F L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
  (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) [inst_12 : w.asIdeal.LiesOver v.asIdeal]
  [inst_13 : q.asIdeal.LiesOver w.asIdeal] [inst_14 : q.asIdeal.LiesOver v.asIdeal],
  Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) ∣
      Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion L q) →
    ∀ (n : ℕ) [NeZero n]
      (y :
        ↑(Langlands.ClassFieldTheory.Local.relativeCohomology (Langlands.Global.CompletionPadic.padicField v).Carrier
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) (n + 2))),
      (CategoryTheory.ConcreteCategory.hom
            (Langlands.ClassFieldTheory.Local.relativeInflation (Langlands.Global.CompletionPadic.padicField v).Carrier
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion L q) (n + 2)))
          y =
        0
```

## Outline of the proofs

By Tate's theorem in the form `ProfiniteCohomology.GroupCoh.exists_cupH_of_tate`, with the subgroup
conditions of the global fundamental class (`fundamentalClass_subgroupConditions`), every class of
`Hⁿ⁺²(Gal(E/F), C_E)` is `u_{E/F} ∪ y` with `y ∈ Hⁿ(Gal(E/F), ℤ)`; rewritten with the scalar pairing
(`ordinaryCup_scalarPairing`). Inflation commutes with the cup product (`Langlands.Tate.ordinaryCup_map`
with the idèle-class inclusion and the identity of `ℤ`) and sends `u_{E/F}` to `[L : E] u_{L/F}`
(`inflation_iff_classes`); `[L : E] y = 0` because `[E : F]` kills `Hⁿ(Gal(E/F), ℤ)`
(`card_smul_groupCohomology`) and divides `[L : E]`. The local statement is
`relativeInflationLinear_eq_zero_of_dvd` for the Library's local invariant family.

## Declarations

`integralInflationIdentity`, `exists_fundamentalClassFamily`, `relativeIdeleClassInflation_eq_zero_of_dvd`, `relativeInflation_adicCompletion_eq_zero_of_dvd`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §11.3, p. 197 (cup product with `u_{L/K}` gives
  isomorphisms `Ĥʳ(G, ℤ) ≅ Ĥʳ⁺²(G, C_L)`), §11.4, p. 199 (killing by inflation).
- J.-P. Serre, *Local Class Field Theory*, ibid., Chapter VI, §2.1, Theorem 1, p. 139.
