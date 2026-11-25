# Archimedean components of idèle cohomology and the localization at a real place

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/RealComponents.lean`, namespace
`Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `ι` a choice of embeddings, `w` an infinite place
of `K`, `E ⊆ Ω` a finite Galois level, `w' = realPlace ι E w` the place of `E` above `w` given by
`ι`, and `K̄_w` the algebraic closure of `K_w`.

* `isConj_conjugate`, `isConj_embedding_mk`: a conjugation for a complex embedding is one for its
  conjugate and for the embedding of its place; `infinitePlaceCompletion_ext`: continuous maps out of
  a completion that agree on the field agree (cohomology along a bijective homomorphism with a
  bijective coefficient map is bijective: `bijective_groupCohomology_map` of the module
  `Langlands.Cohomology.RestrictedProduct`).
* `realCompletionToComplex ι E w : E_{w'} → ℂ`, extending the complex embedding of `ι`
  (`realCompletionToComplex_algebraMap`), continuous, compatible with conjugation, bijective when `w'`
  is complex; `realCompletionToClosure ι E w : E_{w'} → K̄_w` its composite with `ℂ ≃ K̄_w`
  (`realCompletionToClosure_algebraMap`); `comap_realPlace_algebraMap`: `w'` lies over `w`;
  `isComplex_realPlace_of_sq_eq_neg_one`: `w'` is complex if `E` contains `√-1`.
* `realRestrictHom ι E w : Gal(K̄_w/K_w) → Gal(E/K)`; its values fix `w'`
  (`realRestrict_mem_stabilizer`), the conjugation goes to a conjugation of the embedding of `ι`
  (`isConj_realRestrict_closureConj`); `realCompletionToClosure_coordinate_smul`: the coordinate at
  `w'` read in `K̄_w` is equivariant.
* `realIdeleCoefficient ι E w : J_E → K̄_wˣ` and **`realIdeleComparison ι E w n :
  Hⁿ(Gal(E/K), J_E) → Hⁿ(Gal(K̄_w/K_w), K̄_wˣ)`** (the target in the foundations' cochain model).
* `realIdeleComparison_principal`: **on principal classes it is the localization at `w` of the
  inflated class**; `realIdeleComparison_inflation`: **it is compatible with inflation**
  (`comap_realPlace`, `realCompletionToComplex_ideleInclusion`).
* `realStabilizerHom`, `realLocalCoefficient`, `realLocalComparison ι E w n :
  Hⁿ(D_{w'}, E_{w'}ˣ) → Hⁿ(Gal(K̄_w/K_w), K̄_wˣ)`; `realIdeleComparison_eq`: **the real comparison is
  the local component at `w'` followed by `realLocalComparison`**;
  `isComplex_and_isReal_of_ne_one`, `bijective_realLocalComparison`: bijective when `D_{w'}` is
  nontrivial; `injective_realLocalComparison`: injective in positive degree.

## Complete types

```lean
@Langlands.GaloisCohomology.isConj_conjugate : ∀ {k : Type u_1} {L : Type u_2} [inst : Field k] [inst_1 : Field L]
  [inst_2 : Algebra k L] {φ : L →+* ℂ} {σ : Gal(L/k)},
  NumberField.ComplexEmbedding.IsConj φ σ →
    NumberField.ComplexEmbedding.IsConj (NumberField.ComplexEmbedding.conjugate φ) σ
@Langlands.GaloisCohomology.isConj_embedding_mk : ∀ {k : Type u_1} {L : Type u_2} [inst : Field k] [inst_1 : Field L]
  [inst_2 : Algebra k L] {φ : L →+* ℂ} {σ : Gal(L/k)},
  NumberField.ComplexEmbedding.IsConj φ σ →
    NumberField.ComplexEmbedding.IsConj (NumberField.InfinitePlace.mk φ).embedding σ
@Langlands.GaloisCohomology.infinitePlaceCompletion_ext : ∀ {L : Type u_1} [inst : Field L]
  {v : NumberField.InfinitePlace L} {f g : v.Completion → ℂ},
  Continuous f →
    Continuous g →
      (∀ (a : L), f ((algebraMap L v.Completion) a) = g ((algebraMap L v.Completion) a)) →
        ∀ (x : v.Completion), f x = g x
@Langlands.GaloisCohomology.realCompletionToComplex : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) → (Langlands.GaloisCohomology.realPlace ι E w).Completion →+* ℂ
@Langlands.GaloisCohomology.continuous_realCompletionToComplex : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K),
  Continuous ⇑(Langlands.GaloisCohomology.realCompletionToComplex ι E w)
@Langlands.GaloisCohomology.realCompletionToComplex_algebraMap : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K) (a : ↥E),
  (Langlands.GaloisCohomology.realCompletionToComplex ι E w)
      ((algebraMap (↥E) (Langlands.GaloisCohomology.realPlace ι E w).Completion) a) =
    (Langlands.GaloisCohomology.realComplexEmbedding ι E w) a
@Langlands.GaloisCohomology.realCompletionToComplex_star : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) (x y : (Langlands.GaloisCohomology.realPlace ι E w).Completion),
  (NumberField.InfinitePlace.Completion.extensionEmbedding (Langlands.GaloisCohomology.realPlace ι E w)) x =
      star ((NumberField.InfinitePlace.Completion.extensionEmbedding (Langlands.GaloisCohomology.realPlace ι E w)) y) →
    (Langlands.GaloisCohomology.realCompletionToComplex ι E w) x =
      star ((Langlands.GaloisCohomology.realCompletionToComplex ι E w) y)
@Langlands.GaloisCohomology.bijective_realCompletionToComplex : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K),
  (Langlands.GaloisCohomology.realPlace ι E w).IsComplex →
    Function.Bijective ⇑(Langlands.GaloisCohomology.realCompletionToComplex ι E w)
@Langlands.GaloisCohomology.realCompletionToClosure : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) →
                (Langlands.GaloisCohomology.realPlace ι E w).Completion →+* AlgebraicClosure w.Completion
@Langlands.GaloisCohomology.closureToComplex_realCompletionToClosure : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K)
  (x : (Langlands.GaloisCohomology.realPlace ι E w).Completion),
  (Langlands.GaloisCohomology.closureToComplex w) ((Langlands.GaloisCohomology.realCompletionToClosure ι E w) x) =
    (Langlands.GaloisCohomology.realCompletionToComplex ι E w) x
@Langlands.GaloisCohomology.realCompletionToClosure_algebraMap : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K) (a : ↥E),
  (Langlands.GaloisCohomology.realCompletionToClosure ι E w)
      ((algebraMap (↥E) (Langlands.GaloisCohomology.realPlace ι E w).Completion) a) =
    (Langlands.GaloisCohomology.realPlaceEmbedding ι E w) a
@Langlands.GaloisCohomology.comap_realPlace_algebraMap : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realPlace ι E w).comap (algebraMap K ↥E) = w
@Langlands.GaloisCohomology.isComplex_realPlace_of_sq_eq_neg_one : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K) {i : ↥E},
  i ^ 2 = -1 → (Langlands.GaloisCohomology.realPlace ι E w).IsComplex
@Langlands.GaloisCohomology.realRestrictHom : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          Langlands.Galois.PlaceEmbeddings K Ω →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) →
                [IsSepClosure K Ω] → [IsGalois K ↥E] → Gal(AlgebraicClosure w.Completion/w.Completion) →* Gal(↥E/K)
@Langlands.GaloisCohomology.isConj_realRestrict_closureConj : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E]
  (hw : w.IsReal),
  NumberField.ComplexEmbedding.IsConj (Langlands.GaloisCohomology.realComplexEmbedding ι E w)
    (Langlands.GaloisCohomology.realRestrict ι E w (Langlands.GaloisCohomology.closureConj w hw))
@Langlands.GaloisCohomology.realRestrict_mem_stabilizer : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E]
  (σ : Gal(AlgebraicClosure w.Completion/w.Completion)),
  Langlands.GaloisCohomology.realRestrict ι E w σ ∈
    MulAction.stabilizer Gal(↥E/K) (Langlands.GaloisCohomology.realPlace ι E w)
@Langlands.GaloisCohomology.realCompletionToClosure_coordinate_smul : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E]
  [inst_6 : NumberField ↥E] (σ : Gal(AlgebraicClosure w.Completion/w.Completion))
  (x : NumberField.IdeleGroup (NumberField.RingOfIntegers ↥E) ↥E),
  (Langlands.GaloisCohomology.realCompletionToClosure ι E w)
      ↑((Langlands.ClassFieldTheory.Global.ideleInfiniteCoordinate (Langlands.GaloisCohomology.realPlace ι E w))
          (((Langlands.ClassFieldTheory.Global.relativeIdeleAut K ↥E) (Langlands.GaloisCohomology.realRestrict ι E w σ))
            x)) =
    σ
      ((Langlands.GaloisCohomology.realCompletionToClosure ι E w)
        ↑((Langlands.ClassFieldTheory.Global.ideleInfiniteCoordinate (Langlands.GaloisCohomology.realPlace ι E w)) x))
@Langlands.GaloisCohomology.realIdeleCoefficient : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) →
                [inst_4 : IsSepClosure K Ω] →
                  [inst_5 : IsGalois K ↥E] →
                    [inst_6 : NumberField ↥E] →
                      Rep.res (Langlands.GaloisCohomology.realRestrictHom ι E w)
                          (Langlands.ClassFieldTheory.Global.relativeIdeleRepresentation K ↥E) ⟶
                        Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)
@Langlands.GaloisCohomology.realIdeleCoefficient_apply : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E] [inst_6 : NumberField ↥E]
  (x : Additive (NumberField.IdeleGroup (NumberField.RingOfIntegers ↥E) ↥E)),
  ↑(Additive.toMul ((Rep.Hom.hom (Langlands.GaloisCohomology.realIdeleCoefficient ι E w)) x)) =
    (Langlands.GaloisCohomology.realCompletionToClosure ι E w)
      ↑((Langlands.ClassFieldTheory.Global.ideleInfiniteCoordinate (Langlands.GaloisCohomology.realPlace ι E w))
          (Additive.toMul x))
@Langlands.GaloisCohomology.realIdeleComparison : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          Langlands.Galois.PlaceEmbeddings K Ω →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) →
                [IsSepClosure K Ω] →
                  [IsGalois K ↥E] →
                    [inst_6 : NumberField ↥E] →
                      (n : ℕ) →
                        Langlands.ClassFieldTheory.Global.relativeIdeleCohomology K (↥E) n ⟶
                          Langlands.ProfiniteCohomology.cohomology
                            (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) n
@Langlands.GaloisCohomology.realIdeleComparison_principal : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E] [inst_6 : NumberField ↥E]
  [inst_7 : FiniteDimensional K ↥E] (n : ℕ) (a : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology K (↥E) n)),
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.realIdeleComparison ι E w n))
      ((CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.principalIdeleCohomologyMap K (↥E) n))
        a) =
    (Langlands.GaloisCohomology.realBrauerLocalization ι w n)
      ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E n)) a)
@Langlands.GaloisCohomology.comap_realPlace : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) {E : IntermediateField K Ω}
  (w : NumberField.InfinitePlace K) {L : IntermediateField K Ω} (hEL : E ≤ L),
  (Langlands.GaloisCohomology.realPlace ι L w).comap (algebraMap ↥E ↥L) = Langlands.GaloisCohomology.realPlace ι E w
@Langlands.GaloisCohomology.realCompletionToComplex_ideleInclusion : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {E : IntermediateField K Ω} (w : NumberField.InfinitePlace K) {L : IntermediateField K Ω} (hEL : E ≤ L)
  [inst_4 : NumberField ↥E] [inst_5 : NumberField ↥L] (x : NumberField.IdeleGroup (NumberField.RingOfIntegers ↥E) ↥E),
  (Langlands.GaloisCohomology.realCompletionToComplex ι L w)
      ↑((Langlands.ClassFieldTheory.Global.ideleInfiniteCoordinate (Langlands.GaloisCohomology.realPlace ι L w))
          (Langlands.Global.AdelicFunctoriality.ideleInclusion x)) =
    (Langlands.GaloisCohomology.realCompletionToComplex ι E w)
      ↑((Langlands.ClassFieldTheory.Global.ideleInfiniteCoordinate (Langlands.GaloisCohomology.realPlace ι E w)) x)
@Langlands.GaloisCohomology.realIdeleComparison_inflation : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) {E : IntermediateField K Ω}
  (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] {L : IntermediateField K Ω} (hEL : E ≤ L)
  [inst_5 : IsGalois K ↥E] [inst_6 : IsGalois K ↥L] [inst_7 : NumberField ↥E] [inst_8 : NumberField ↥L] (n : ℕ)
  (z : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology K (↥E) n)),
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.realIdeleComparison ι L w n))
      ((CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.relativeIdeleInflation K (↥E) (↥L) n))
        z) =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.realIdeleComparison ι E w n)) z
@Langlands.GaloisCohomology.realStabilizerHom : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) →
                [IsSepClosure K Ω] →
                  [IsGalois K ↥E] →
                    Gal(AlgebraicClosure w.Completion/w.Completion) →*
                      ↥(MulAction.stabilizer Gal(↥E/K) (Langlands.GaloisCohomology.realPlace ι E w))
@Langlands.GaloisCohomology.realLocalCoefficient : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) →
                [inst_4 : IsSepClosure K Ω] →
                  [inst_5 : IsGalois K ↥E] →
                    [inst_6 : NumberField ↥E] →
                      Rep.res (Langlands.GaloisCohomology.realStabilizerHom ι E w)
                          (Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation K
                            (Langlands.GaloisCohomology.realPlace ι E w)) ⟶
                        Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)
@Langlands.GaloisCohomology.realLocalComparison : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
            (E : IntermediateField K Ω) →
              (w : NumberField.InfinitePlace K) →
                [IsSepClosure K Ω] →
                  [IsGalois K ↥E] →
                    [inst_6 : NumberField ↥E] →
                      (n : ℕ) →
                        groupCohomology
                            (Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation K
                              (Langlands.GaloisCohomology.realPlace ι E w))
                            n ⟶
                          Langlands.ProfiniteCohomology.cohomology
                            (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) n
@Langlands.GaloisCohomology.realIdeleComparison_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E] [inst_6 : NumberField ↥E]
  (n : ℕ),
  Langlands.GaloisCohomology.realIdeleComparison ι E w n =
    CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.ideleInfiniteLocalMap (Langlands.GaloisCohomology.realPlace ι E w) n)
      (Langlands.GaloisCohomology.realLocalComparison ι E w n)
@Langlands.GaloisCohomology.isComplex_and_isReal_of_ne_one : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K) {c : Gal(↥E/K)},
  c ∈ MulAction.stabilizer Gal(↥E/K) (Langlands.GaloisCohomology.realPlace ι E w) →
    c ≠ 1 →
      NumberField.ComplexEmbedding.IsConj (Langlands.GaloisCohomology.realPlace ι E w).embedding c ∧
        (Langlands.GaloisCohomology.realPlace ι E w).IsComplex ∧ w.IsReal
@Langlands.GaloisCohomology.bijective_realLocalComparison : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E] [inst_6 : NumberField ↥E],
  (∃ c ∈ MulAction.stabilizer Gal(↥E/K) (Langlands.GaloisCohomology.realPlace ι E w), c ≠ 1) →
    ∀ (n : ℕ),
      Function.Bijective ⇑(CategoryTheory.ConcreteCategory.hom (Langlands.GaloisCohomology.realLocalComparison ι E w n))
@Langlands.GaloisCohomology.injective_realLocalComparison : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω)
  (w : NumberField.InfinitePlace K) [inst_4 : IsSepClosure K Ω] [inst_5 : IsGalois K ↥E] [inst_6 : NumberField ↥E]
  (n : ℕ),
  Function.Injective
    ⇑(CategoryTheory.ConcreteCategory.hom (Langlands.GaloisCohomology.realLocalComparison ι E w (n + 1)))
```

## Outline of the proofs

`realCompletionToComplex` is Mathlib's `extensionEmbedding` of `w'`, or its complex conjugate when the
embedding Mathlib attaches to `w' = mk φ` is `φ̄` (`InfinitePlace.embedding_mk_eq`). Equivariance is
checked in `ℂ`: `Gal(K̄_w/K_w)` is `{1, closureConj}` at a real place and trivial at a complex one,
the image of `closureConj` is a conjugation of `w'`, and the Library's
`extensionEmbedding_ideleInfiniteCoordinate_of_isConj` describes its action on coordinates. The
principal formula follows the proof of `brauerLocalization_unitsInflation`
(`FiniteComparison.lean`): `unitsInflation_apply_eq`, composition of maps in the foundations
(`map_comp`), naturality of the comparison with `groupCohomology` (`map_comp_toGroupCohomology`) and
equality of the coefficient functions. Inflation compatibility reduces, through
`galRestrictOfLE_restrictNormalHom`, to the agreement of two continuous maps out of a completion on
the field (`infinitePlaceCompletion_ext`), the coordinate of an included idele being given by the
Library's `infiniteCompletionMap`. If `D_{w'}` contains `c ≠ 1`, then `c` is a conjugation of `w'`,
`w'` is complex and `w` real; `realStabilizerHom` sends `closureConj` to `c` and is bijective, and
`realLocalCoefficient` is bijective. If `D_{w'}` is trivial its cohomology vanishes in positive
degree.

## Declarations

`isConj_conjugate`, `isConj_embedding_mk`, `infinitePlaceCompletion_ext`, `realCompletionToComplex`, `continuous_realCompletionToComplex`, `realCompletionToComplex_algebraMap`, `realCompletionToComplex_star`, `bijective_realCompletionToComplex`, `realCompletionToClosure`, `closureToComplex_realCompletionToClosure`, `realCompletionToClosure_algebraMap`, `comap_realPlace_algebraMap`, `isComplex_realPlace_of_sq_eq_neg_one`, `realRestrictHom`, `isConj_realRestrict_closureConj`, `realRestrict_mem_stabilizer`, `realCompletionToClosure_coordinate_smul`, `realIdeleCoefficient`, `realIdeleCoefficient_apply`, `realIdeleComparison`, `realIdeleComparison_principal`, `comap_realPlace`, `realCompletionToComplex_ideleInclusion`, `realIdeleComparison_inflation`, `realStabilizerHom`, `realLocalCoefficient`, `realLocalComparison`, `realIdeleComparison_eq`, `isComplex_and_isReal_of_ne_one`, `bijective_realLocalComparison`, `injective_realLocalComparison`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §7, Proposition 7.2, p. 176 (the local component through
  Shapiro's lemma), §11.4, p. 198.
