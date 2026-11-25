# Local class and order class at an unramified place

`Langlands/GaloisCohomology/Global/Units/LocalOrder.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `v` a finite place, `M / K` a finite Galois extension of number fields and
`j : M →ₐ[K] K̄_v` an embedding; `w = placeOfAlgHom j` is the place of `M` defined by `j`.

- `placeExponent v j : Mˣ → ℤ` is the exponent of the normalized valuation at `w`
  (`valuation_eq_exp_placeExponent`); it is additive, compatible with automorphisms
  (`placeExponent_comp_algEquiv`) and, at places unramified over `K`, with towers
  (`placeExponent_algebraMap`), and invariant under the decomposition group
  (`placeExponent_decompositionHom`).
- `placeOfAlgHom_comp_eq_iff`: `j ∘ τ` defines the same place as `j` exactly when `τ` lies in the image
  of the decomposition homomorphism of `j`.
- `localUnitsHomOf v j : Res(Mˣ) ⟶ K̄_vˣ` and `localExponentHom v j : Res(Mˣ) ⟶ ℤ` are the coefficient
  maps along the decomposition homomorphism `Gal(K̄_v/K_v) → Gal(M/K)` of `j`.

**Theorem** (`map_localUnitsHomOf_eq_zero_iff`). If `w` is unramified over `v`, a class
`b ∈ H²(Gal(M/K), Mˣ)` has zero image in `H²(K_v, K̄_vˣ)` if and only if its image in
`H²(K_v, ℤ)` (through `placeExponent`) is zero.

Proof. Both maps factor through the completion `M_w`: `b ↦ c ∈ H²(Gal(M_w/K_v), M_wˣ)`
(`map_localUnitsHomOf`, `map_localExponentHom`, from `decompositionHom_eq_comp`). Inflation
`H²(Gal(M_w/K_v), M_wˣ) → H²(K_v, K̄_vˣ)` is injective (`unitsTowerMap_two_injective`, from the
Library's `finiteInvariant_unitsTowerMap` and the invariant at the finite level), and so is inflation
`H²(Gal(M_w/K_v), ℤ) → H²(K_v, ℤ)` (`map_trivialResHom_two_injective`, through `ℚ/ℤ`). For `w`
unramified, `H²(Gal(M_w/K_v), U_w) = 0` (the Library's `isZero_H2_localUnits`), so the order map
`H²(Gal(M_w/K_v), M_wˣ) → H²(Gal(M_w/K_v), ℤ)` is injective
(`coeffMap_completionExponentHom_two_injective`).

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
@Langlands.GaloisCohomology.trivialResHom : {G Γ : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      [inst_2 : Group Γ] →
        [inst_3 : TopologicalSpace Γ] →
          (r : G →ₜ* Γ) →
            (A : Type u_1) →
              [inst_4 : AddCommGroup A] →
                Rep.res (↑r) (Langlands.GaloisCohomology.trivialModule Γ A) ⟶
                  Langlands.GaloisCohomology.trivialModule G A
@Langlands.GaloisCohomology.trivialResHom_hom_apply : ∀ {G Γ : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : Group Γ] [inst_3 : TopologicalSpace Γ] (r : G →ₜ* Γ) (A : Type u_1) [inst_4 : AddCommGroup A] (a : A),
  (Rep.Hom.hom (Langlands.GaloisCohomology.trivialResHom r A)) a = a
@Langlands.GaloisCohomology.trivialResSequence : {G Γ : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      [inst_2 : Group Γ] →
        [inst_3 : TopologicalSpace Γ] →
          (r : G →ₜ* Γ) →
            (Langlands.GaloisCohomology.trivialSequence Γ).map (Rep.resFunctor ↑r) ⟶
              Langlands.GaloisCohomology.trivialSequence G
@Langlands.GaloisCohomology.map_trivialResHom_one_injective : ∀ {G Γ : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : Group Γ] [inst_4 : TopologicalSpace Γ]
  [inst_5 : IsTopologicalGroup Γ] (r : G →ₜ* Γ),
  Function.Surjective ⇑r →
    ∀ (A : Type u_1) [inst_6 : AddCommGroup A],
      Function.Injective
        ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map r (Langlands.GaloisCohomology.trivialResHom r A) 1))
@Langlands.GaloisCohomology.map_trivialResHom_two_injective : ∀ {G Γ : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : Group Γ] [inst_4 : TopologicalSpace Γ]
  [inst_5 : IsTopologicalGroup Γ] (r : G →ₜ* Γ) [CompactSpace G] [TotallyDisconnectedSpace G] [DiscreteTopology Γ]
  [Finite Γ],
  Function.Surjective ⇑r →
    Function.Injective
      ⇑(ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map r (Langlands.GaloisCohomology.trivialResHom r (ULift.{u_1, 0} ℤ)) 2))
Langlands.GaloisCohomology.integralTrivialHom : (Γ : Type u_1) →
  [inst : Group Γ] →
    Rep.trivial Langlands.ClassFieldTheory.Local.IntegerScalars Γ Langlands.ClassFieldTheory.Local.IntegerScalars ⟶
      Langlands.GaloisCohomology.trivialModule Γ (ULift.{u_1, 0} ℤ)
@Langlands.GaloisCohomology.groupCohomologyTwoMap : {Γ : Type u_1} →
  [inst : Group Γ] →
    {A B : Rep.{u_1, u_1, u_1} Langlands.ClassFieldTheory.Local.IntegerScalars Γ} →
      (A ⟶ B) → (groupCohomology A 2 ⟶ groupCohomology B 2)
@Langlands.GaloisCohomology.completionAlgebraOf : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [inst_3 : NumberField M] →
              [inst_4 : Algebra K M] →
                (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) →
                  Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
                    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
@Langlands.GaloisCohomology.isScalarTower_completionAlgebraOf : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1}
  [inst_2 : Field M] [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)),
  IsScalarTower (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
@Langlands.GaloisCohomology.placeExponent : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [NumberField M] →
              [inst_4 : Algebra K M] →
                (M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) → Mˣ → ℤ
@Langlands.GaloisCohomology.placeExponent_mul : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) (x y : Mˣ),
  Langlands.GaloisCohomology.placeExponent v j (x * y) =
    Langlands.GaloisCohomology.placeExponent v j x + Langlands.GaloisCohomology.placeExponent v j y
@Langlands.GaloisCohomology.placeExponent_one : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)),
  Langlands.GaloisCohomology.placeExponent v j 1 = 0
@Langlands.GaloisCohomology.placeExponentHom : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [NumberField M] →
              [inst_4 : Algebra K M] →
                (M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) →
                  Additive Mˣ →+ ULift.{u_1, 0} ℤ
@Langlands.GaloisCohomology.valuation_eq_exp_placeExponent : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) (x : Mˣ),
  (IsDedekindDomain.HeightOneSpectrum.valuation M ↑(Langlands.Galois.placeOfAlgHom j)) ↑x =
    WithZero.exp (Langlands.GaloisCohomology.placeExponent v j x)
@Langlands.GaloisCohomology.placeOfAlgHom_comp_algEquiv : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) (g : Gal(M/K)),
  ↑(Langlands.Galois.placeOfAlgHom (j.comp ↑g)) =
    (Langlands.Global.AdelicFunctoriality.finitePlaceEquiv g.toRingEquiv) ↑(Langlands.Galois.placeOfAlgHom j)
@Langlands.GaloisCohomology.placeExponent_comp_algEquiv : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) (g : Gal(M/K)) (x : Mˣ),
  Langlands.GaloisCohomology.placeExponent v (j.comp ↑g) x =
    Langlands.GaloisCohomology.placeExponent v j ((Units.map ↑g) x)
@Langlands.GaloisCohomology.placeOfAlgHom_under : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) {L : Type u_1}
  [inst_5 : Field L] [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L M]
  [inst_9 : IsScalarTower K L M],
  IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers L) ↑(Langlands.Galois.placeOfAlgHom j) =
    ↑(Langlands.Galois.placeOfAlgHom (j.comp (IsScalarTower.toAlgHom K L M)))
@Langlands.GaloisCohomology.placeExponent_algebraMap : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) {L : Type u_1}
  [inst_5 : Field L] [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L M]
  [inst_9 : IsScalarTower K L M],
  Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) (↑(Langlands.Galois.placeOfAlgHom j)).asIdeal →
    ∀ (x : Lˣ),
      Langlands.GaloisCohomology.placeExponent v j ((Units.map ↑(Algebra.algebraMap L M)) x) =
        Langlands.GaloisCohomology.placeExponent v (j.comp (IsScalarTower.toAlgHom K L M)) x
@Langlands.GaloisCohomology.placeOfAlgHom_comp_eq_iff : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M]
  (τ : Gal(M/K)),
  Langlands.Galois.placeOfAlgHom (j.comp ↑τ) = Langlands.Galois.placeOfAlgHom j ↔
    τ ∈ (↑(Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j)).range
@Langlands.GaloisCohomology.localDecompositionHomOf : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [inst_3 : NumberField M] →
              [inst_4 : Algebra K M] →
                (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) →
                  [IsGalois K M] →
                    Gal(IsDedekindDomain.HeightOneSpectrum.adicCompletion M
                          ↑(Langlands.Galois.placeOfAlgHom j)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) →ₜ*
                      Gal(M/K)
@Langlands.GaloisCohomology.decompositionHom_eq_comp : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M],
  Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j =
    (Langlands.GaloisCohomology.localDecompositionHomOf v j).comp
      (Langlands.BrauerComparison.normalKrullRestriction (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
@Langlands.GaloisCohomology.localUnitsHomOf : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [inst_3 : Algebra K M] →
              (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) →
                [inst_4 : IsGalois K M] →
                  Rep.res
                      (↑(Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j))
                      (Langlands.GaloisCohomology.unitsModule K M) ⟶
                    Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
@Langlands.GaloisCohomology.placeExponent_decompositionHom : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M]
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  (x : Mˣ),
  Langlands.GaloisCohomology.placeExponent v j
      (((Langlands.GaloisCohomology.galUnitsHom K M)
          ((Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j) σ))
        x) =
    Langlands.GaloisCohomology.placeExponent v j x
@Langlands.GaloisCohomology.localExponentHom : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [NumberField M] →
              [inst_4 : Algebra K M] →
                (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) →
                  [inst_5 : IsGalois K M] →
                    Rep.res
                        (↑(Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j))
                        (Langlands.GaloisCohomology.unitsModule K M) ⟶
                      Langlands.GaloisCohomology.trivialModule
                        Gal(AlgebraicClosure
                            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
                              v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                        (ULift.{u_1, 0} ℤ)
@Langlands.GaloisCohomology.localExponentHom_hom_apply : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M]
  (x : Additive Mˣ),
  (Rep.Hom.hom (Langlands.GaloisCohomology.localExponentHom v j)) x =
    { down := Langlands.GaloisCohomology.placeExponent v j (Additive.toMul x) }
@Langlands.GaloisCohomology.completionUnitsHomOf : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [inst_3 : NumberField M] →
              [inst_4 : Algebra K M] →
                (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) →
                  [inst_5 : IsGalois K M] →
                    Rep.res (↑(Langlands.GaloisCohomology.localDecompositionHomOf v j))
                        (Langlands.GaloisCohomology.unitsModule K M) ⟶
                      Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                        (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
@Langlands.GaloisCohomology.completionExponentHom : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
        {M : Type u_1} →
          [inst_2 : Field M] →
            [inst_3 : NumberField M] →
              [inst_4 : Algebra K M] →
                (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) →
                  Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                      (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j)) ⟶
                    Langlands.GaloisCohomology.trivialModule
                      Gal(IsDedekindDomain.HeightOneSpectrum.adicCompletion M
                          ↑(Langlands.Galois.placeOfAlgHom j)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                      (ULift.{u_1, 0} ℤ)
@Langlands.GaloisCohomology.map_localUnitsHomOf : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M]
  (b : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K M) 2)),
  (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map
          (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j)
          (Langlands.GaloisCohomology.localUnitsHomOf v j) 2))
      b =
    (ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.unitsTowerMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) 2))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.localDecompositionHomOf v j)
            (Langlands.GaloisCohomology.completionUnitsHomOf v j) 2))
        b)
@Langlands.GaloisCohomology.map_localExponentHom : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M]
  (b : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K M) 2)),
  (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map
          (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j)
          (Langlands.GaloisCohomology.localExponentHom v j) 2))
      b =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.map
          (Langlands.BrauerComparison.normalKrullRestriction (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
          (Langlands.GaloisCohomology.trivialResHom
            (Langlands.BrauerComparison.normalKrullRestriction (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
              (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
            (ULift.{u_1, 0} ℤ))
          2))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.localDecompositionHomOf v j)
            (CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.completionUnitsHomOf v j)
              (Langlands.GaloisCohomology.completionExponentHom v j))
            2))
        b)
@Langlands.GaloisCohomology.unitsTowerMap_two_injective : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M],
  Function.Injective
    ⇑(ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.unitsTowerMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion M ↑(Langlands.Galois.placeOfAlgHom j))
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) 2))
@Langlands.GaloisCohomology.coeffMap_completionExponentHom_two_injective : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {M : Type u_1}
  [inst_2 : Field M] [inst_3 : NumberField M] [inst_4 : Algebra K M]
  {j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)} [inst_5 : IsGalois K M],
  (↑(Langlands.Galois.placeOfAlgHom j)).asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 →
    Function.Injective
      ⇑(ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.completionExponentHom v j) 2))
@Langlands.GaloisCohomology.map_localUnitsHomOf_eq_zero_iff : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : Type u_1} [inst_2 : Field M]
  [inst_3 : NumberField M] [inst_4 : Algebra K M]
  (j : M →ₐ[K] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) [inst_5 : IsGalois K M],
  (↑(Langlands.Galois.placeOfAlgHom j)).asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 →
    ∀ (b : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K M) 2)),
      (ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.map
                (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j)
                (Langlands.GaloisCohomology.localUnitsHomOf v j) 2))
            b =
          0 ↔
        (ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.map
                (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) j)
                (Langlands.GaloisCohomology.localExponentHom v j) 2))
            b =
          0
```

## Literature

- page reference to be added (the unramified computation `H²(G(M_w|K_v), U_w) = 0` is the Library's
  `isZero_H2_localUnits`).

## Source and licence

New. The corresponding statement of the source (`BrauerOrd.lean`, `BrauerLocalVal.lean` in
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`) is proved there by an explicit computation with unramified cocycles; this
file uses the Library's local theory instead, and contains no text of the source.
