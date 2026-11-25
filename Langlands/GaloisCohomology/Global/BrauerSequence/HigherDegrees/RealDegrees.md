# `Hʳ(Gal(Ω/K), Ωˣ)` for `r ≥ 4`: the real places

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/RealDegrees.lean`, namespace
`Langlands.GaloisCohomology`.

* `subsingleton_cohomology_of_isComplex`: at a complex place `w` the foundations' cohomology of
  `K̄_wˣ` vanishes in positive degree.
* `ideleInfiniteLocalMap_principal_eq_zero`: the infinite components of the image in idèle cohomology
  of a class whose inflation has trivial real localizations vanish.
* `unitsInflation_eq_zero_of_realBrauerLocalization`, `eq_zero_of_realBrauerLocalization_eq_zero`:
  **a class of `Hⁿ⁺⁴(Gal(Ω/K), Ωˣ)` with trivial localizations at the real places is zero.**
* `exists_realBrauerLocalization_eq_of_sq_eq_neg_one`, `exists_realBrauerLocalization_eq`: **every
  family of classes `βʷ ∈ Hⁿ⁺⁴(Gal(K̄_w/K_w), K̄_wˣ)`, `w` real, is the family of real localizations of
  a class of `Hⁿ⁺⁴(Gal(Ω/K), Ωˣ)`.**
* `bijective_realBrauerLocalization`: **for `r ≥ 4` the localization
  `Hʳ(Gal(Ω/K), Ωˣ) → ∏_{w real} Hʳ(Gal(K̄_w/K_w), K̄_wˣ)` is bijective.**

## Complete types

```lean
@Langlands.GaloisCohomology.subsingleton_cohomology_of_isComplex : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] {w : NumberField.InfinitePlace K},
  w.IsComplex →
    ∀ (n : ℕ),
      Subsingleton
        ↑(Langlands.ProfiniteCohomology.cohomology
            (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) (n + 1))
@Langlands.GaloisCohomology.ideleInfiniteLocalMap_principal_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : FiniteDimensional K ↥E]
  [inst_6 : IsGalois K ↥E] [inst_7 : NumberField ↥E] (n : ℕ)
  (a : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology K (↥E) (n + 1))),
  (∀ (w : NumberField.InfinitePlace K),
      w.IsReal →
        (Langlands.GaloisCohomology.realBrauerLocalization ι w (n + 1))
            ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E (n + 1))) a) =
          0) →
    ∀ (w : NumberField.InfinitePlace K),
      (CategoryTheory.ConcreteCategory.hom
            (Langlands.GaloisCohomology.ideleInfiniteLocalMap (Langlands.GaloisCohomology.realPlace ι E w) (n + 1)))
          ((CategoryTheory.ConcreteCategory.hom
              (Langlands.ClassFieldTheory.Global.principalIdeleCohomologyMap K (↥E) (n + 1)))
            a) =
        0
@Langlands.GaloisCohomology.unitsInflation_eq_zero_of_realBrauerLocalization : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : FiniteDimensional K ↥E]
  [inst_6 : IsGalois K ↥E] (n : ℕ) (a : ↑(groupCohomology (Langlands.GaloisCohomology.unitsModule K ↥E) (n + 4))),
  (∀ (w : NumberField.InfinitePlace K),
      w.IsReal →
        (Langlands.GaloisCohomology.realBrauerLocalization ι w (n + 4))
            ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E (n + 4))) a) =
          0) →
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E (n + 4))) a = 0
@Langlands.GaloisCohomology.eq_zero_of_realBrauerLocalization_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (n : ℕ)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) (n + 4))),
  (∀ (w : NumberField.InfinitePlace K),
      w.IsReal → (Langlands.GaloisCohomology.realBrauerLocalization ι w (n + 4)) x = 0) →
    x = 0
@Langlands.GaloisCohomology.exists_realBrauerLocalization_eq_of_sq_eq_neg_one : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [FiniteDimensional K ↥E] [IsGalois K ↥E]
  [NumberField ↥E] {i : ↥E},
  i ^ 2 = -1 →
    ∀ (n : ℕ)
      (β :
        (w : { w : NumberField.InfinitePlace K // w.IsReal }) →
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.unitsModule (↑w).Completion (AlgebraicClosure (↑w).Completion)) (n + 4))),
      ∃ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) (n + 4))),
        ∀ (w : { w : NumberField.InfinitePlace K // w.IsReal }),
          (Langlands.GaloisCohomology.realBrauerLocalization ι (↑w) (n + 4)) x = β w
@Langlands.GaloisCohomology.exists_realBrauerLocalization_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (n : ℕ)
  (β :
    (w : { w : NumberField.InfinitePlace K // w.IsReal }) →
      ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.unitsModule (↑w).Completion (AlgebraicClosure (↑w).Completion)) (n + 4))),
  ∃ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) (n + 4))),
    ∀ (w : { w : NumberField.InfinitePlace K // w.IsReal }),
      (Langlands.GaloisCohomology.realBrauerLocalization ι (↑w) (n + 4)) x = β w
@Langlands.GaloisCohomology.bijective_realBrauerLocalization : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (r : ℕ),
  4 ≤ r →
    Function.Bijective
      fun (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) r))
        (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
      (Langlands.GaloisCohomology.realBrauerLocalization ι (↑w) r) x
```

## Outline of the proofs

*Injectivity.* Let `x = infl a` with `a ∈ Hʳ(Gal(E/K), Eˣ)` and `b` the image of `a` in
`Hʳ(Gal(E/K), J_E)`. Its infinite components vanish (`injective_realLocalComparison`,
`realIdeleComparison_eq`, `realIdeleComparison_principal`); its finite components vanish outside a
finite set `T` (`finite_ideleLocalMap_ne_zero`). Choose `L ⊇ E` with local degrees above `T`
divisible by `[E : K]²` (`exists_le_localDegreesDvd_of_finset`); then
`[E_w : K_v] ∣ [L_q : E_w]` and the finite components of the inflation of `b` vanish
(`ideleLocalMap_relativeIdeleInflation`, `relativeInflation_adicCompletion_eq_zero_of_dvd`), the
infinite ones too (`realIdeleComparison_inflation`), so the inflation of `b` is zero
(`eq_zero_of_ideleLocalMap_eq_zero`). The inflation of `a` to `L` is therefore `δ c`,
`c ∈ Hʳ⁻¹(Gal(L/K), C_L)`, and `c` dies at a level `L'` with `[L : K] ∣ [L' : L]`
(`relativeIdeleClassInflation_eq_zero_of_dvd`), so the inflation of `a` to `L'` is zero.
*Surjectivity.* If `K` has no real place there is nothing to prove. Otherwise `E = K(i)` is a
quadratic Galois level at which every `w'` is complex, so each `realLocalComparison` is bijective; let
`y = Σ_w s_{w'}(γʷ)` with `γʷ` the preimage of `βʷ` and `s_{w'}` the infinite local sections; the
components of `y` are the `γʷ` (orthogonality). Its image in `Hʳ(Gal(E/K), C_E)` dies at a level `L`
with `[E : K] ∣ [L : E]`, so the inflation of `y` to `L` is the image of a class `a'` of
`Hʳ(Gal(L/K), Lˣ)` (exactness), and `infl a'` has real localizations
`realIdeleComparison (infl y) = realLocalComparison(γʷ) = βʷ`.

## Declarations

`subsingleton_cohomology_of_isComplex`, `ideleInfiniteLocalMap_principal_eq_zero`, `unitsInflation_eq_zero_of_realBrauerLocalization`, `eq_zero_of_realBrauerLocalization_eq_zero`, `exists_realBrauerLocalization_eq_of_sq_eq_neg_one`, `exists_realBrauerLocalization_eq`, `bijective_realBrauerLocalization`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. It
replaces the source's `bijective_realLocalization` (`GlobalClassFormation/HighUnits.lean`), proved
there through limit modules, by a proof at finite levels from the Library's class field theory.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §11.4, pp. 198–199 (the computation of `Ĥʳ(G, Lˣ)` from
  the idèles and idèle classes).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013), Chapter VIII, §1, Proposition (8.1.7), p. 430 (`Hⁱ(k, I) ≅ ⊕_p Hⁱ(k_p, k̄_pˣ)`;
  for `i ≥ 3` only the real places contribute).
