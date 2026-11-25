# The cohomology of the idèles of a finite Galois extension is local

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/IdeleDecomposition.lean`, namespace
`Langlands.GaloisCohomology`.

Let `E / F` be a finite Galois extension of number fields and `J_E` its idèle group (the Library's
`relativeIdeleRepresentation F E`). Choose a finite place `wf v` of `E` above every finite place `v`
of `F` and an infinite place `wi v` above every infinite place `v` (`(wi v).comap (algebraMap F E) = v`).

* `comap_infinitePlaceEquiv`, `exists_infinitePlaceEquiv_eq`: `Gal(E/F)` preserves the place of `F`
  below an infinite place of `E` and acts transitively on the places above it.
* `ideleBlock`, `ideleIntegralBlock`, `ideleIntegralBlockInclusion`, `ideleBlockProjection`: the block
  of a place `v` of `F` is `Coind(E_wˣ)` (`Coind(U_w)` its integral part at a finite place), coinduced
  along `decompositionHom v (wf v)` or along the stabilizer of `wi v`, and the projection of `J_E` to
  it is the Library's semilocal projection.
* `isRestrictedProduct_ideleBlock`: **`J_E` is the restricted product of the blocks** with respect to
  the integral blocks.
* `finite_not_isZero_ideleIntegralBlock`: the integral blocks have vanishing cohomology in positive
  degree outside the finitely many ramified places and the infinite places.
* `ideleInfiniteLocalMap w n`: the local component `Hⁿ(Gal(E/F), J_E) → Hⁿ(D_w, E_wˣ)` at an infinite
  place.
* `eq_zero_of_ideleLocalMap_eq_zero`: **a class of `Hⁿ⁺¹(Gal(E/F), J_E)` whose local components at the
  chosen places above all places of `F` vanish is zero**; `finite_ideleLocalMap_ne_zero`: only finitely
  many finite local components of a class are nonzero.
* `ideleInfiniteLocalSection w n`: a section of the infinite local map
  (`ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap`), and the **orthogonality**
  `ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap_of_ne` at places in different orbits.

Together with the local vanishing this is the injectivity and finite-support half of the
isomorphism `Hⁿ(Gal(E/F), J_E) ≅ ⊕_v Hⁿ(D_w, E_wˣ)`, `n ≥ 1`.

## Complete types

```lean
@Langlands.GaloisCohomology.comap_infinitePlaceEquiv : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (g : Gal(E/F)) (w : NumberField.InfinitePlace E),
  ((Langlands.Global.AdelicFunctoriality.infinitePlaceEquiv g.toRingEquiv) w).comap (algebraMap F E) =
    w.comap (algebraMap F E)
@Langlands.GaloisCohomology.exists_infinitePlaceEquiv_eq : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] [NumberField E] [IsGalois F E] {w w' : NumberField.InfinitePlace E},
  w.comap (algebraMap F E) = w'.comap (algebraMap F E) →
    ∃ (g : Gal(E/F)), (Langlands.Global.AdelicFunctoriality.infinitePlaceEquiv g.toRingEquiv) w = w'
@Langlands.GaloisCohomology.ideleBlock : {F E : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      [inst_2 : Field E] →
        [NumberField E] →
          [inst_4 : Algebra F E] →
            [IsGalois F E] →
              (wf :
                  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
                    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) →
                [hwf :
                    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                      (wf v).asIdeal.LiesOver v.asIdeal] →
                  (NumberField.InfinitePlace F → NumberField.InfinitePlace E) →
                    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) ⊕ NumberField.InfinitePlace F →
                      Rep.{u_1, u_1, u_1} Langlands.NormalizedTwoCocycle.CoefficientScalars Gal(E/F)
@Langlands.GaloisCohomology.ideleIntegralBlock : {F E : Type u_1} →
  [inst : Field F] →
    [NumberField F] →
      [inst_2 : Field E] →
        [NumberField E] →
          [inst_4 : Algebra F E] →
            [IsGalois F E] →
              (wf :
                  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
                    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) →
                [hwf :
                    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                      (wf v).asIdeal.LiesOver v.asIdeal] →
                  (NumberField.InfinitePlace F → NumberField.InfinitePlace E) →
                    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) ⊕ NumberField.InfinitePlace F →
                      Rep.{u_1, u_1, u_1} Langlands.NormalizedTwoCocycle.CoefficientScalars Gal(E/F)
@Langlands.GaloisCohomology.ideleIntegralBlockInclusion : {F E : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      [inst_2 : Field E] →
        [inst_3 : NumberField E] →
          [inst_4 : Algebra F E] →
            [inst_5 : IsGalois F E] →
              (wf :
                  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
                    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) →
                [hwf :
                    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                      (wf v).asIdeal.LiesOver v.asIdeal] →
                  (wi : NumberField.InfinitePlace F → NumberField.InfinitePlace E) →
                    (i :
                        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) ⊕
                          NumberField.InfinitePlace F) →
                      Langlands.GaloisCohomology.ideleIntegralBlock wf wi i ⟶
                        Langlands.GaloisCohomology.ideleBlock wf wi i
@Langlands.GaloisCohomology.ideleBlockProjection : {F E : Type u_1} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      [inst_2 : Field E] →
        [inst_3 : NumberField E] →
          [inst_4 : Algebra F E] →
            [inst_5 : IsGalois F E] →
              (wf :
                  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
                    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) →
                [hwf :
                    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                      (wf v).asIdeal.LiesOver v.asIdeal] →
                  (wi : NumberField.InfinitePlace F → NumberField.InfinitePlace E) →
                    (i :
                        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) ⊕
                          NumberField.InfinitePlace F) →
                      Langlands.ClassFieldTheory.Global.relativeIdeleRepresentation F E ⟶
                        Langlands.GaloisCohomology.ideleBlock wf wi i
@Langlands.GaloisCohomology.eq_of_ideleBlockProjection_eq : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (wf :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
  [hwf : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (wf v).asIdeal.LiesOver v.asIdeal]
  (wi : NumberField.InfinitePlace F → NumberField.InfinitePlace E),
  (∀ (v : NumberField.InfinitePlace F), (wi v).comap (algebraMap F E) = v) →
    ∀ {x y : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleRepresentation F E)},
      (∀ (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) ⊕ NumberField.InfinitePlace F),
          (Rep.Hom.hom (Langlands.GaloisCohomology.ideleBlockProjection wf wi i)) x =
            (Rep.Hom.hom (Langlands.GaloisCohomology.ideleBlockProjection wf wi i)) y) →
        x = y
@Langlands.GaloisCohomology.ideleSemilocalProjection_mem_localUnits : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal]
  (x : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleRepresentation F E)),
  (∀ (u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [u.asIdeal.LiesOver v.asIdeal],
      (Langlands.ClassFieldTheory.Global.ideleCoordinate u) (Additive.toMul x) ∈
        Langlands.ClassFieldTheory.Global.localUnits u) →
    ∀ (g : Gal(E/F)),
      Additive.toMul (↑((Rep.Hom.hom (Langlands.ClassFieldTheory.Global.ideleSemilocalProjection v w)) x) g) ∈
        Langlands.ClassFieldTheory.Global.localUnits w
@Langlands.GaloisCohomology.finite_placeBelow_image : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))),
  T.Finite →
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) |
        ∃ u ∈ T, Langlands.ClassFieldTheory.Global.placeBelow F u = v}.Finite
@Langlands.GaloisCohomology.finite_placeBelow_preimage : ∀ {F E : Type u_1} [inst : Field F] [NumberField F]
  [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))),
  S.Finite →
    {u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E) |
        Langlands.ClassFieldTheory.Global.placeBelow F u ∈ S}.Finite
@Langlands.GaloisCohomology.isRestrictedProduct_ideleBlock : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (wf :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
  [hwf : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (wf v).asIdeal.LiesOver v.asIdeal]
  (wi : NumberField.InfinitePlace F → NumberField.InfinitePlace E),
  (∀ (v : NumberField.InfinitePlace F), (wi v).comap (algebraMap F E) = v) →
    Langlands.Cohomology.IsRestrictedProduct (Langlands.GaloisCohomology.ideleBlockProjection wf wi)
      (Langlands.GaloisCohomology.ideleIntegralBlockInclusion wf wi)
@Langlands.GaloisCohomology.ideleInfiniteLocalMap : {F E : Type u_1} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : NumberField E] →
        [inst_3 : Algebra F E] →
          (w : NumberField.InfinitePlace E) →
            (n : ℕ) →
              Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E n ⟶
                groupCohomology (Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation F w) n
@Langlands.GaloisCohomology.map_ideleSemilocalProjection_eq_zero : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal]
  (n : ℕ) (x : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E n)),
  (CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.ideleLocalMap v w n)) x = 0 →
    (CategoryTheory.ConcreteCategory.hom
          (groupCohomology.map (MonoidHom.id Gal(E/F)) (Langlands.ClassFieldTheory.Global.ideleSemilocalProjection v w)
            n))
        x =
      0
@Langlands.GaloisCohomology.map_infiniteSemilocalProjection_eq_zero : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : Field E] [inst_2 : NumberField E] [inst_3 : Algebra F E] (w : NumberField.InfinitePlace E) (n : ℕ)
  (x : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E n)),
  (CategoryTheory.ConcreteCategory.hom (Langlands.GaloisCohomology.ideleInfiniteLocalMap w n)) x = 0 →
    (CategoryTheory.ConcreteCategory.hom
          (groupCohomology.map (MonoidHom.id Gal(E/F))
            (Langlands.ClassFieldTheory.Global.infiniteSemilocalProjection F w) n))
        x =
      0
@Langlands.GaloisCohomology.finite_setOf_ramified_wf : ∀ {F E : Type u_1} [inst : Field F] [NumberField F]
  [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
  (wf :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
  [hwf : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (wf v).asIdeal.LiesOver v.asIdeal],
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) |
      (wf v).asIdeal.ramificationIdx (NumberField.RingOfIntegers F) ≠ 1}.Finite
@Langlands.GaloisCohomology.finite_not_isZero_ideleIntegralBlock : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (wf :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
  [hwf : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (wf v).asIdeal.LiesOver v.asIdeal]
  (wi : NumberField.InfinitePlace F → NumberField.InfinitePlace E) (n : ℕ),
  {i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) ⊕ NumberField.InfinitePlace F |
      ¬CategoryTheory.Limits.IsZero
          (groupCohomology (Langlands.GaloisCohomology.ideleIntegralBlock wf wi i) (n + 1))}.Finite
@Langlands.GaloisCohomology.finite_ideleLocalMap_ne_zero : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : NumberField F]
  [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (wf :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
  [hwf : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (wf v).asIdeal.LiesOver v.asIdeal]
  (wi : NumberField.InfinitePlace F → NumberField.InfinitePlace E),
  (∀ (v : NumberField.InfinitePlace F), (wi v).comap (algebraMap F E) = v) →
    ∀ (n : ℕ) (x : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E (n + 1))),
      {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) |
          (CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.ideleLocalMap v (wf v) (n + 1))) x ≠
            0}.Finite
@Langlands.GaloisCohomology.eq_zero_of_ideleLocalMap_eq_zero : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (wf :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
  [hwf : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (wf v).asIdeal.LiesOver v.asIdeal]
  (wi : NumberField.InfinitePlace F → NumberField.InfinitePlace E),
  (∀ (v : NumberField.InfinitePlace F), (wi v).comap (algebraMap F E) = v) →
    ∀ (n : ℕ) (x : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E (n + 1))),
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
          (CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.ideleLocalMap v (wf v) (n + 1))) x =
            0) →
        (∀ (v : NumberField.InfinitePlace F),
            (CategoryTheory.ConcreteCategory.hom (Langlands.GaloisCohomology.ideleInfiniteLocalMap (wi v) (n + 1))) x =
              0) →
          x = 0
@Langlands.GaloisCohomology.ideleInfiniteLocalSection : {F E : Type u_1} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : NumberField E] →
        [inst_3 : Algebra F E] →
          (w : NumberField.InfinitePlace E) →
            [Fintype (Gal(E/F) ⧸ (MulAction.stabilizer Gal(E/F) w).subtype.range)] →
              (n : ℕ) →
                groupCohomology (Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation F w) n ⟶
                  Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E n
@Langlands.GaloisCohomology.ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : Field E] [inst_2 : NumberField E] [inst_3 : Algebra F E] (w : NumberField.InfinitePlace E)
  [inst_4 : Fintype (Gal(E/F) ⧸ (MulAction.stabilizer Gal(E/F) w).subtype.range)] (n : ℕ),
  CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.ideleInfiniteLocalSection w n)
      (Langlands.GaloisCohomology.ideleInfiniteLocalMap w n) =
    CategoryTheory.CategoryStruct.id
      (groupCohomology (Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation F w) n)
@Langlands.GaloisCohomology.infiniteSemilocalSection_comp_infiniteLocalProjection_of_ne : ∀ {F E : Type u_1}
  [inst : Field F] [inst_1 : Field E] [inst_2 : NumberField E] [inst_3 : Algebra F E] (w : NumberField.InfinitePlace E)
  [inst_4 : Fintype (Gal(E/F) ⧸ (MulAction.stabilizer Gal(E/F) w).subtype.range)] (w' : NumberField.InfinitePlace E),
  (∀ (g : Gal(E/F)), (Langlands.Global.AdelicFunctoriality.infinitePlaceEquiv g.toRingEquiv) w' ≠ w) →
    CategoryTheory.CategoryStruct.comp
        ((Rep.resFunctor (MulAction.stabilizer Gal(E/F) w').subtype).map
          (Langlands.ClassFieldTheory.Global.infiniteSemilocalSection F w))
        (Langlands.ClassFieldTheory.Global.infiniteLocalProjection F w') =
      0
@Langlands.GaloisCohomology.ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap_of_ne : ∀ {F E : Type u_1}
  [inst : Field F] [inst_1 : Field E] [inst_2 : NumberField E] [inst_3 : Algebra F E] (w : NumberField.InfinitePlace E)
  [inst_4 : Fintype (Gal(E/F) ⧸ (MulAction.stabilizer Gal(E/F) w).subtype.range)] (w' : NumberField.InfinitePlace E),
  (∀ (g : Gal(E/F)), (Langlands.Global.AdelicFunctoriality.infinitePlaceEquiv g.toRingEquiv) w' ≠ w) →
    ∀ (n : ℕ),
      CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.ideleInfiniteLocalSection w n)
          (Langlands.GaloisCohomology.ideleInfiniteLocalMap w' n) =
        0
```

## Outline of the proofs

The four conditions of `IsRestrictedProduct` are read on coordinates. An idele is determined by its
finite coordinates and its infinite adèle part (`idele_ext`); the semilocal projection at `wf v`
determines the coordinates at all places above `v` (`ideleCoordinate_eq_of_ideleSemilocalProjection_eq`
and its infinite analogue with `exists_infinitePlaceEquiv_eq`). The projection of an idele at `v` lies
in `Coind(U_w)` as soon as its coordinates above `v` are units, which fails only above finitely many
`v` (`finite_setOf_ideleCoordinate_not_mem_localUnits`). Given components `p v`, the idele with
coordinates those of the semilocal sections of the `p v` (`ideleOfCoordinates`,
`ideleOfInfiniteCoordinates`) has these components, because the semilocal projection only depends on
the coordinates above `v` (`ideleCoordinate_relativeIdeleAut_eq`). The two statements on cohomology
are then `IsRestrictedProduct.eq_zero_of_map_eq_zero` and `IsRestrictedProduct.finite_map_ne_zero` (of the
module `Langlands.Cohomology.RestrictedProduct`)
with `isZero_groupCohomology_coindLocalUnits`, the local maps factoring through the projection to the
block and Shapiro's isomorphism (`ideleLocalMap_eq`, `map_infiniteSemilocalProjection_comp_shapiroMapOf`).
The infinite sections are the Library's `infiniteSemilocalSection` after the inverse Shapiro
isomorphism; orthogonality is the vanishing of the coordinate at `w'` of `g • ι_w(y)` when
`g⁻¹ w' ≠ w`.

## Declarations

`comap_infinitePlaceEquiv`, `exists_infinitePlaceEquiv_eq`, `ideleBlock`, `ideleIntegralBlock`, `ideleIntegralBlockInclusion`, `ideleBlockProjection`, `eq_of_ideleBlockProjection_eq`, `ideleSemilocalProjection_mem_localUnits`, `finite_placeBelow_image`, `finite_placeBelow_preimage`, `isRestrictedProduct_ideleBlock`, `ideleInfiniteLocalMap`, `map_ideleSemilocalProjection_eq_zero`, `map_infiniteSemilocalProjection_eq_zero`, `finite_setOf_ramified_wf`, `finite_not_isZero_ideleIntegralBlock`, `finite_ideleLocalMap_ne_zero`, `eq_zero_of_ideleLocalMap_eq_zero`, `ideleInfiniteLocalSection`, `ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap`, `infiniteSemilocalSection_comp_infiniteLocalProjection_of_ne`, `ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap_of_ne`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §7, Proposition 7.2, p. 176 (Shapiro's lemma for
  `∏_{w|v} L_wˣ`), Proposition 7.3, p. 177 (`Ĥʳ(G, J_L) ≅ ⊕_v Ĥʳ(Gᵛ, Lᵛˣ)`; the file proves the
  injectivity and the finite support of this map in ordinary cohomology of positive degree).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013), Chapter VIII, §1, Proposition (8.1.7), p. 430 (the same in the limit).
