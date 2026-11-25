# Inflation from `G_S` to the absolute Galois group

`Langlands/GaloisCohomology/Global/Units/Inflation.lean`, namespace `Langlands.GaloisCohomology`.

For a continuous surjective homomorphism `f : G → P` of profinite groups which is a quotient map, and
a morphism `φ : B → A` identifying the `P`-module `B` with the invariants of `ker f` in `A`,
inflation-restriction holds for the map along `f` (`map_injective_of_isQuotientMap`,
`range_map_eq_ker_res_of_isQuotientMap`), provided `Hⁱ(ker f, A) = 0` for `1 ≤ i < q`.

Applied to `Gal(Ω/K) → G_S = Gal(K_S/K)` and `K_Sˣ → Ωˣ` this gives
`maximalUnitsInflation K Ω S n : Hⁿ(G_S, K_Sˣ) → Hⁿ(Gal(Ω/K), Ωˣ)`. In degree `2` it is injective
(`maximalUnitsInflation_two_injective`, Hilbert 90 for `Ω / K_S`), its image is the kernel of the
restriction to `Gal(Ω/K_S)` (`mem_range_maximalUnitsInflation_two_iff`), and a class which dies in a
subextension `E ⊆ K_S` is inflated from `G_S` (`exists_maximalUnitsInflation_eq`).

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.exists_map_eq_iso_comp_infl : ∀ {k G P : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [inst_4 : Group P] [inst_5 : TopologicalSpace P]
  [inst_6 : IsTopologicalGroup P] (f : G →ₜ* P),
  Function.Surjective ⇑f →
    Topology.IsQuotientMap ⇑f →
      ∀ {B : Rep.{u_1, u_1, u_1} k P} [inst_7 : Langlands.IsSmoothRep B] {A : Rep.{u_1, u_1, u_1} k G}
        [inst_8 : Langlands.IsSmoothRep A] (φ : Rep.res (↑f) B ⟶ A),
        Function.Injective ⇑(Rep.Hom.hom φ) →
          (∀ (a : ↑A), (∀ s ∈ (↑f).ker, (A.ρ s) a = a) → ∃ (b : ↑(Rep.res (↑f) B)), (Rep.Hom.hom φ) b = a) →
            ∀ (n : ℕ),
              ∃ (I :
                Langlands.ProfiniteCohomology.cohomology B n ⟶
                  Langlands.ProfiniteCohomology.cohomology (A.quotientToInvariants (↑f).ker) n),
                CategoryTheory.IsIso I ∧
                  Langlands.ProfiniteCohomology.map f φ n =
                    CategoryTheory.CategoryStruct.comp I (Langlands.ProfiniteCohomology.infl A (↑f).ker n)
@Langlands.GaloisCohomology.map_injective_of_isQuotientMap : ∀ {k G P : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [inst_6 : Group P] [inst_7 : TopologicalSpace P] [inst_8 : IsTopologicalGroup P] [T2Space P] (f : G →ₜ* P),
  Function.Surjective ⇑f →
    Topology.IsQuotientMap ⇑f →
      ∀ {B : Rep.{u_1, u_1, u_1} k P} [inst_10 : Langlands.IsSmoothRep B] {A : Rep.{u_1, u_1, u_1} k G}
        [inst_11 : Langlands.IsSmoothRep A] (φ : Rep.res (↑f) B ⟶ A),
        Function.Injective ⇑(Rep.Hom.hom φ) →
          (∀ (a : ↑A), (∀ s ∈ (↑f).ker, (A.ρ s) a = a) → ∃ (b : ↑(Rep.res (↑f) B)), (Rep.Hom.hom φ) b = a) →
            ∀ {q : ℕ},
              q ≠ 0 →
                (∀ (i : ℕ),
                    0 < i →
                      i < q →
                        CategoryTheory.Limits.IsZero
                          (Langlands.ProfiniteCohomology.cohomology (Rep.res (↑f).ker.subtype A) i)) →
                  Function.Injective ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map f φ q))
@Langlands.GaloisCohomology.range_map_eq_ker_res_of_isQuotientMap : ∀ {k G P : Type u_1} [inst : CommRing k]
  [inst_1 : Group G] [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [inst_6 : Group P] [inst_7 : TopologicalSpace P] [inst_8 : IsTopologicalGroup P]
  [T2Space P] (f : G →ₜ* P),
  Function.Surjective ⇑f →
    Topology.IsQuotientMap ⇑f →
      ∀ {B : Rep.{u_1, u_1, u_1} k P} [inst_10 : Langlands.IsSmoothRep B] {A : Rep.{u_1, u_1, u_1} k G}
        [inst_11 : Langlands.IsSmoothRep A] (φ : Rep.res (↑f) B ⟶ A),
        Function.Injective ⇑(Rep.Hom.hom φ) →
          (∀ (a : ↑A), (∀ s ∈ (↑f).ker, (A.ρ s) a = a) → ∃ (b : ↑(Rep.res (↑f) B)), (Rep.Hom.hom φ) b = a) →
            ∀ {q : ℕ},
              q ≠ 0 →
                (∀ (i : ℕ),
                    0 < i →
                      i < q →
                        CategoryTheory.Limits.IsZero
                          (Langlands.ProfiniteCohomology.cohomology (Rep.res (↑f).ker.subtype A) i)) →
                  (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map f φ q)).range =
                    (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.res A (↑f).ker q)).ker
Langlands.GaloisCohomology.maximalUnitsHom : (K Ω : Type u_1) →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S))
                  (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) ⟶
                Langlands.GaloisCohomology.unitsModule K Ω
Langlands.GaloisCohomology.maximalUnitsInflation : (K Ω : Type u_1) →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsGalois K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (n : ℕ) →
                ↑(Langlands.ProfiniteCohomology.cohomology
                      (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
                      n) →+
                  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) n)
@Langlands.GaloisCohomology.maximalUnitsInflation_apply : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (x :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n)),
  (Langlands.GaloisCohomology.maximalUnitsInflation K Ω S n) x =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map (Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)
          (Langlands.GaloisCohomology.maximalUnitsHom K Ω S) n))
      x
@Langlands.GaloisCohomology.mem_ker_quotientMap_iff : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (σ : Gal(Ω/K)),
  σ ∈ (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker ↔
    ∀ x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S, σ x = x
@Langlands.GaloisCohomology.maximalUnitsHom_injective : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Function.Injective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.maximalUnitsHom K Ω S))
@Langlands.GaloisCohomology.exists_maximalUnitsHom_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (a : ↑(Langlands.GaloisCohomology.unitsModule K Ω)),
  (∀ s ∈ (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker,
      ((Langlands.GaloisCohomology.unitsModule K Ω).ρ s) a = a) →
    ∃ (b :
      ↑(Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S))
          (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)))),
      (Rep.Hom.hom (Langlands.GaloisCohomology.maximalUnitsHom K Ω S)) b = a
@Langlands.GaloisCohomology.isZero_cohomology_one_ker_quotientMap : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  CategoryTheory.Limits.IsZero
    (Langlands.ProfiniteCohomology.cohomology
      (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker.subtype
        (Langlands.GaloisCohomology.unitsModule K Ω))
      1)
@Langlands.GaloisCohomology.maximalUnitsInflation_two_injective : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  Function.Injective ⇑(Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
@Langlands.GaloisCohomology.mem_range_maximalUnitsInflation_two_iff : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
  x ∈ (Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2).range ↔
    (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.res (Langlands.GaloisCohomology.unitsModule K Ω)
            (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker 2))
        x =
      0
@Langlands.GaloisCohomology.res_ker_quotientMap_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
  (ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.unitsRestriction K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) Ω 2))
        x =
      0 →
    (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.res (Langlands.GaloisCohomology.unitsModule K Ω)
            (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker 2))
        x =
      0
@Langlands.GaloisCohomology.unitsRestriction_maximal_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_5 : IsSepClosure K Ω],
  ∀ E ≤ Langlands.Galois.maximalUnramifiedOutside K Ω S,
    ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
      (Langlands.GaloisCohomology.brauerRestriction E) x = 0 →
        (ModuleCat.Hom.hom
              (Langlands.GaloisCohomology.unitsRestriction K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) Ω 2))
            x =
          0
@Langlands.GaloisCohomology.exists_maximalUnitsInflation_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_5 : IsSepClosure K Ω],
  ∀ E ≤ Langlands.Galois.maximalUnramifiedOutside K Ω S,
    ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
      (Langlands.GaloisCohomology.brauerRestriction E) x = 0 →
        ∃ (z :
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)),
          (Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2) z = x
```

## Literature

- page reference to be added (inflation-restriction).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BrauerSplit.lean` (lines 27–333). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the inflation-restriction
statements are proved for an abstract quotient map from the foundations' `infl_injective_of_isZero`
and `range_infl_eq_ker_res`; `gsBrauerInfl` is `maximalUnitsInflation`.
