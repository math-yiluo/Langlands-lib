# Local invariants of inflated Brauer classes at the finite places

`Langlands/GaloisCohomology/Global/BrauerSequence/FiniteComparison.lean`, namespace
`Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `ι : PlaceEmbeddings K Ω`, `E ⊆ Ω` a finite
Galois extension of `K` and `v` a finite place of `K`. The embedding `ι.finite v` restricted to `E`
(`placeEmbedding`) determines a place `w = localPlace ι E v` of `E` above `v` and an embedding of the
completion `E_w` into `K̄_v` (`completionAlgebra`).

- `localBrauerInvariant_congr`: the Library's local Brauer invariant of a field does not depend on
  the proofs that a given topology and valuation make it a nonarchimedean local field.
- `finiteInvariant_unitsTowerMap`: for a finite Galois extension `L/K_v` inside `K̄_v` and a
  local invariant family `I` with the arithmetic normalization and compatibility with inflation, the
  invariant `finiteInvariant v` of the inflation to `Gal(K̄_v/K_v)` of `b ∈ H²(Gal(L/K_v), Lˣ)` is the
  Library's relative invariant `I.relative (padicField v) L b`.
- `unitsInflation_apply_eq`: for any Galois extension `L / K` and a finite Galois level `E ⊆ L`, the
  foundations' inflation `unitsInflation E n` is `isoGroupCohomology⁻¹` followed by
  `unitsTowerMap K E L n`.
- `localDecompositionHom`, `localUnitsHom`, `unitsLocalMap_eq_map`: the Library's local component map
  `unitsLocalMap v w n` is the map along the decomposition homomorphism at `w` with coefficients
  `Eˣ → E_wˣ`.
- `brauerLocalization_unitsInflation`: the localization at `v` of a class inflated from
  `H²(Gal(E/K), Eˣ)` is the inflation from `E_w` of its Library local component at `w`.
- `localInvariant_unitsInflation`: hence `localInvariant ι v (unitsInflation E 2 a)` is the Library's
  `Reciprocity.finiteLocalInvariant v w I a`.

## Complete types

```lean
@Langlands.GaloisCohomology.localBrauerInvariant_congr : ∀ {F : Type u_1} [inst : Field F] {T₁ T₂ : TopologicalSpace F}
  {V₁ V₂ : ValuativeRel F} (h₁ : IsNonarchimedeanLocalField F) (h₂ : IsNonarchimedeanLocalField F),
  T₁ = T₂ →
    V₁ = V₂ →
      ∀ (x : BrauerGroup F),
        (Langlands.ClassFieldTheory.Local.localBrauerInvariant F) x =
          (Langlands.ClassFieldTheory.Local.localBrauerInvariant F) x

@Langlands.GaloisCohomology.finiteInvariant_unitsTowerMap : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (L : Type u_1) [inst_2 : Field L]
  [inst_3 : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L]
  [inst_4 : FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L]
  [inst_5 : IsGalois (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L]
  [inst_6 : Algebra L (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))]
  [inst_7 :
    IsScalarTower (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))]
  (I : Langlands.ClassFieldTheory.Local.InvariantFamily (Langlands.Global.CompletionPadic.residuePrime v)),
  I.ArithmeticNormalization →
    I.InflationCompatibility →
      ∀
        (b :
          ↑(Langlands.ClassFieldTheory.Local.relativeCohomology (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
              L 2)),
        (Langlands.GaloisCohomology.finiteInvariant v)
            ((ModuleCat.Hom.hom
                (Langlands.GaloisCohomology.unitsTowerMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L
                  (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) 2))
              ((ModuleCat.Hom.hom
                  (Langlands.ProfiniteCohomology.isoGroupCohomology
                      (Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L)
                      2).inv)
                b)) =
          (I.relative (Langlands.Global.CompletionPadic.padicField v) L) b

@Langlands.GaloisCohomology.unitsInflation_apply_eq : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : IsGalois K L] (E : IntermediateField K L) [inst_4 : FiniteDimensional K ↥E]
  [inst_5 : IsGalois K ↥E] (n : ℕ) (a : ↑(groupCohomology (Langlands.GaloisCohomology.unitsModule K ↥E) n)),
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E n)) a =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsTowerMap K (↥E) L n))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.isoGroupCohomology (Langlands.GaloisCohomology.unitsModule K ↥E) n).inv)
        a)

@Langlands.GaloisCohomology.placeEmbedding : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          Langlands.Galois.PlaceEmbeddings K Ω →
            (E : IntermediateField K Ω) →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                ↥E →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)

@Langlands.GaloisCohomology.localPlace : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          Langlands.Galois.PlaceEmbeddings K Ω →
            (E : IntermediateField K Ω) →
              [NumberField ↥E] →
                IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
                  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E)

@Langlands.GaloisCohomology.liesOver_localPlace : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  [inst_4 : NumberField ↥E] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  (Langlands.GaloisCohomology.localPlace ι E v).asIdeal.LiesOver v.asIdeal

@Langlands.GaloisCohomology.completionAlgebra : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              [inst_4 : NumberField ↥E] →
                (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                  Algebra
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥E)
                      (Langlands.GaloisCohomology.localPlace ι E v))
                    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))

@Langlands.GaloisCohomology.isScalarTower_completionAlgebra : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) [inst_4 : NumberField ↥E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  IsScalarTower (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥E) (Langlands.GaloisCohomology.localPlace ι E v))
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))

@Langlands.GaloisCohomology.localDecompositionHom : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              [IsGalois K ↥E] →
                [inst_5 : NumberField ↥E] →
                  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                    Gal(IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥E)
                          (Langlands.GaloisCohomology.localPlace ι E
                            v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) →ₜ*
                      Gal(↥E/K)

@Langlands.GaloisCohomology.localUnitsHom : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              [inst_4 : IsGalois K ↥E] →
                [inst_5 : NumberField ↥E] →
                  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
                    Rep.res (↑(Langlands.GaloisCohomology.localDecompositionHom ι E v))
                        (Langlands.GaloisCohomology.unitsModule K ↥E) ⟶
                      Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                        (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥E)
                          (Langlands.GaloisCohomology.localPlace ι E v))

@Langlands.GaloisCohomology.unitsLocalMap_eq_map : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  [inst_4 : IsGalois K ↥E] [inst_5 : NumberField ↥E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ),
  Langlands.ClassFieldTheory.Global.unitsLocalMap v (Langlands.GaloisCohomology.localPlace ι E v) n =
    groupCohomology.map (↑(Langlands.GaloisCohomology.localDecompositionHom ι E v))
      (Langlands.GaloisCohomology.localUnitsHom ι E v) n

@Langlands.GaloisCohomology.brauerLocalization_unitsInflation : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : FiniteDimensional K ↥E]
  [inst_6 : IsGalois K ↥E] [inst_7 : NumberField ↥E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (a : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology K (↥E) 2)),
  (Langlands.GaloisCohomology.brauerLocalization ι v 2)
      ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E 2)) a) =
    (ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.unitsTowerMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥E) (Langlands.GaloisCohomology.localPlace ι E v))
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) 2))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.isoGroupCohomology
              (Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥E) (Langlands.GaloisCohomology.localPlace ι E v)))
              2).inv)
        ((ModuleCat.Hom.hom
            (Langlands.ClassFieldTheory.Global.unitsLocalMap v (Langlands.GaloisCohomology.localPlace ι E v) 2))
          a))

@Langlands.GaloisCohomology.localInvariant_unitsInflation : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) [inst_5 : FiniteDimensional K ↥E] [inst_6 : IsGalois K ↥E] [inst_7 : NumberField ↥E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (I : (p : ℕ) → [inst : Fact (Nat.Prime p)] → Langlands.ClassFieldTheory.Local.InvariantFamily p),
  (∀ (p : ℕ) [inst : Fact (Nat.Prime p)], (I p).ArithmeticNormalization) →
    (∀ (p : ℕ) [inst : Fact (Nat.Prime p)], (I p).InflationCompatibility) →
      ∀ (a : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology K (↥E) 2)),
        (Langlands.GaloisCohomology.localInvariant ι v)
            ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E 2)) a) =
          (Langlands.ClassFieldTheory.Global.Reciprocity.finiteLocalInvariant v
              (Langlands.GaloisCohomology.localPlace ι E v) I)
            a
```

## Outline of the proofs

`finiteInvariant_unitsTowerMap`: write `b` as the Library's relative class of a Brauer class of
`K_v` split by `L` (`exists_relativeClass_eq`); its inflation is the Library's continuous inflation
read in the cochain model (`unitsModuleContinuousEquiv_symm_relativeToContinuous`), i.e. the image of
the Brauer class under `brauerEquiv` (`brauerContinuousEquiv_at_chart`); the local theory's invariant
of that image is `localBrauerInvariant` of the Brauer class (`invariant_brauerEquiv`), which the
Library's comparison `relativeInvariant_eq_localBrauerInvariant`
(`ClassFieldTheory/Local/PadicBrauerInvariantComparison.lean`) identifies
with the relative invariant, after replacing the completion's topology and valuation by those of
`FiniteCompletion` (`completion_topology_eq`, `FiniteCompletion.topologicalData_valuativeRel_eq`,
`localBrauerInvariant_congr`). `brauerLocalization_unitsInflation`: both sides are maps of the
foundations' cohomology along continuous homomorphisms; `map_comp` and `map_congr` reduce the
claim to the equality of the composite homomorphisms
`Gal(K̄_v/K_v) → Gal(Ω/K) → Gal(E/K)` and `Gal(K̄_v/K_v) → Gal(E_w/K_v) → Gal(E/K)`, which holds
because `completionEmbeddingOfAlgHom` extends the embedding of `E`.

## Declarations

`localBrauerInvariant_congr`, `finiteInvariant_unitsTowerMap`, `unitsInflation_apply_eq`,
`placeEmbedding`, `localPlace`, `liesOver_localPlace`, `completionAlgebra`,
`isScalarTower_completionAlgebra`, `localDecompositionHom`, `localUnitsHom`, `unitsLocalMap_eq_map`,
`brauerLocalization_unitsInflation`, `localInvariant_unitsInflation`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. The local
invariants of the source are replaced by the local theory's `Local.invariant`, compared here with the
Library's relative invariants.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): Corollary (7.1.4), p. 375 (the invariant map
  `inv : H²(k̄|k) ≅ ℚ/ℤ` and its restriction `inv_{K|k} : H²(K|k) ≅ (1/[K:k])ℤ/ℤ` to a finite Galois
  level).
