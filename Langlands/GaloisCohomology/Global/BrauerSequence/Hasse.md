# Hasse principle and reciprocity law for `H²(Gal(Ω/K), Ωˣ)`

`Langlands/GaloisCohomology/Global/BrauerSequence/Hasse.lean`, namespace
`Langlands.GaloisCohomology`.

**Independence of the embeddings.** `brauerLocalization_eq`, `realBrauerLocalization_eq`: for two
choices `ι, ι'` of embeddings the localizations differ by an automorphism of `Ω` and agree on
cohomology classes (inner conjugation acts trivially); hence `localInvariant_eq`,
`realLocalInvariant_eq`.

**Every place comes from an embedding.** `exists_algHom_comp_val_eq`: an embedding of an
intermediate field into an algebraically closed field extends to `Ω`. `exists_localPlace_eq`: every
finite place of a finite Galois `E ⊆ Ω` above `v` is `localPlace ι' E v` for some `ι'`;
`exists_realPlace_eq`: every infinite place of `E` above `w` is `realPlace ι' E w` for some `ι'`.

**The Library's local invariant family.** `brauerInvariantFamily p` is a local invariant family for
the prime `p` forming a relative class formation with the arithmetic normalization, chosen from the
Library's `localRelativeClassFormation` (`brauerInvariantFamily_spec`).

**Hasse principle.** `eq_zero_of_brauerLocalization_eq_zero'`: a class of `H²(Gal(Ω/K), Ωˣ)` whose
localizations at all places vanish is zero.

**Reciprocity law.** `localInvariant_finite_support_and_sum_eq_zero`: the local invariants of a class
at the finite places have finite support, and the sum of all local invariants is zero.

## Complete types

```lean
@Langlands.GaloisCohomology.brauerLocalization_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] (ι ι' : Langlands.Galois.PlaceEmbeddings K Ω)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ),
  Langlands.GaloisCohomology.brauerLocalization ι' v n = Langlands.GaloisCohomology.brauerLocalization ι v n

@Langlands.GaloisCohomology.realBrauerLocalization_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] (ι ι' : Langlands.Galois.PlaceEmbeddings K Ω)
  (w : NumberField.InfinitePlace K) (n : ℕ),
  Langlands.GaloisCohomology.realBrauerLocalization ι' w n = Langlands.GaloisCohomology.realBrauerLocalization ι w n

@Langlands.GaloisCohomology.localInvariant_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] (ι ι' : Langlands.Galois.PlaceEmbeddings K Ω)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  Langlands.GaloisCohomology.localInvariant ι' v = Langlands.GaloisCohomology.localInvariant ι v

@Langlands.GaloisCohomology.realLocalInvariant_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω] (ι ι' : Langlands.Galois.PlaceEmbeddings K Ω)
  (w : NumberField.InfinitePlace K),
  Langlands.GaloisCohomology.realLocalInvariant ι' w = Langlands.GaloisCohomology.realLocalInvariant ι w

@Langlands.GaloisCohomology.exists_algHom_comp_val_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] [Algebra.IsAlgebraic K Ω] {M : Type u_1} [inst_4 : Field M] [inst_5 : Algebra K M]
  [IsAlgClosed M] (E : IntermediateField K Ω) (j : ↥E →ₐ[K] M), ∃ (J : Ω →ₐ[K] M), J.comp E.val = j

@Langlands.GaloisCohomology.exists_localPlace_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω] (E : IntermediateField K Ω) [inst_5 : NumberField ↥E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (w : Langlands.Global.AdelicFunctoriality.FinitePlacesAbove (↥E) v),
  ∃ (ι' : Langlands.Galois.PlaceEmbeddings K Ω), Langlands.GaloisCohomology.localPlace ι' E v = ↑w

@Langlands.GaloisCohomology.closureToComplex_algebraMap_base : ∀ {K : Type u_1} [inst : Field K]
  (w : NumberField.InfinitePlace K) (k : K),
  (Langlands.GaloisCohomology.closureToComplex w) ((algebraMap K (AlgebraicClosure w.Completion)) k) = w.embedding k

@Langlands.GaloisCohomology.exists_realPlace_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω] (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) (u : NumberField.InfinitePlace ↥E) [u.LiesOver w],
  ∃ (ι' : Langlands.Galois.PlaceEmbeddings K Ω), Langlands.GaloisCohomology.realPlace ι' E w = u

@Langlands.GaloisCohomology.liesOver_realPlace : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω] (E : IntermediateField K Ω) [FiniteDimensional K ↥E]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K),
  (Langlands.GaloisCohomology.realPlace ι E w).LiesOver w

Langlands.GaloisCohomology.brauerInvariantFamily : (p : ℕ) →
  [inst : Fact (Nat.Prime p)] → Langlands.ClassFieldTheory.Local.InvariantFamily p

Langlands.GaloisCohomology.brauerInvariantFamily_spec : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
  (Langlands.GaloisCohomology.brauerInvariantFamily p).RelativeClassFormation ∧
    (Langlands.GaloisCohomology.brauerInvariantFamily p).ArithmeticNormalization

@Langlands.GaloisCohomology.eq_zero_of_brauerLocalization_eq_zero' : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (Langlands.GaloisCohomology.brauerLocalization ι v 2) x = 0) →
    (∀ (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x = 0) → x = 0

@Langlands.GaloisCohomology.localInvariant_finite_support_and_sum_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
  (Function.support fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) =>
        (Langlands.GaloisCohomology.localInvariant ι v) x).Finite ∧
    ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          (Langlands.GaloisCohomology.localInvariant ι v) x +
        ∑ w : NumberField.InfinitePlace K, Langlands.GaloisCohomology.realLocalInvariant ι w x =
      0
```

## Outline of the proofs

Every class is inflated from a finite Galois level `E` (`exists_unitsInflation_eq`). For each place of
`E` choose `ι'` realizing it (`exists_localPlace_eq`, `exists_realPlace_eq`, via
`exists_placeOfAlgHom_eq` of `Langlands.Galois.RestrictedRamification.Localization` and the
extension lemma); by the independence lemmas and
`localInvariant_unitsInflation`, `realLocalInvariant_unitsInflation` the local invariants of the class
are the Library's local invariants of the finite-level class at all places of `E`. The Library's
Hasse principle at finite level (`Reciprocity.eq_zero_of_local_eq_zero` with
`ideleClassH1Vanishing`, the injectivity of the relative invariants given by `RelativeImages`) and
its reciprocity law (`globalReciprocity_of`) give the two theorems.

## Declarations

`brauerLocalization_eq`, `realBrauerLocalization_eq`, `localInvariant_eq`, `realLocalInvariant_eq`,
`exists_algHom_comp_val_eq`, `exists_localPlace_eq`, `closureToComplex_algebraMap_base`,
`exists_realPlace_eq`, `liesOver_realPlace`, `brauerInvariantFamily`, `brauerInvariantFamily_spec`,
`eq_zero_of_brauerLocalization_eq_zero'`, `localInvariant_finite_support_and_sum_eq_zero`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. It replaces
the source's `brauerLocal_injective` (`GlobalClassFormation/EqZeroOfBrauerLocalApplyEqZero.lean`) and
`brauerSumInv_eq_zero` (`GlobalClassFormation/SumInvariants.lean`), which are proved there from the
source's idèle class formation, by proofs from the Library's global class field theory at finite
levels.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): Theorem (8.1.17), p. 437 (exact sequence
  `0 → Br(k) → ⊕_p Br(k_p) → ℚ/ℤ → 0`).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), Chapter I, §4, p. 48
  (the choice of an embedding of `K^s` into `K_v^s` for every prime `v`, identifying `G_v` with a
  decomposition group: here `PlaceEmbeddings`).
