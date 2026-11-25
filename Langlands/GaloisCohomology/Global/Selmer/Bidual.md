# The double dual of a family of local conditions

`Langlands/GaloisCohomology/Global/Selmer/Bidual.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `S` a finite set of finite places containing the places above `N ≥ 1`,
`M` a finite smooth `G_S`-module killed by `N`, `M' = Hom(M, μ_N)` and `M'' = Hom(M', μ_N)`.
Evaluation `M → M''` is an isomorphism (`toBidualIso`). A family of local conditions is carried along
an isomorphism of modules (`LocalConditions.map`), and the Selmer group of the carried family is the
image of the Selmer group (`LocalConditions.selmerGroup_map`). For a family `L` of conditions for `M`,
the dual of the dual family is `L` carried to `M''` (`LocalConditions.dual_dual`), and so
`Sel_{(L^⊥)^⊥}(M'')` is the image of `Sel_L(M)` (`LocalConditions.selmerGroup_dual_dual`).

The point is the sign rule of the local pairings in degree one: for `x ∈ H¹(K_v, M)` and
`y ∈ H¹(K_v, M')`, `⟨y, x⟩_{M'} = -⟨x, y⟩_M` with `x` read in `M''`
(`ptLocalPairing_dual_toDualDual` of the module `Langlands.GaloisCohomology.CompactSupport.NineTerm`; at
the places of `S` and the real places
`localPairing_dual_toBidualIso`, `realLocalPairing_dual_toBidualIso`). The orthogonal for `⟨·,·⟩_{M'}`
of a subgroup of `H¹(K_v, M')` is then the image of its left orthogonal for `⟨·,·⟩_M`
(`rightOrthogonal_eq_map_leftOrthogonal`). Localization commutes with coefficient maps
(`localization_coeffMap`). `M''` and its local restrictions are smooth (`isSmoothRep_dual_dual`,
`isSmoothRep_localModule_dual_dual`, `isSmoothRep_realLocalModule_dual_dual`).

```lean
theorem rightOrthogonal_eq_map_leftOrthogonal (P : A →+ B →+ QZ) (P' : B →+ C →+ QZ)
    (e : A ≃+ C) (h : ∀ a b, P' b (e a) = -P a b) (Y : AddSubgroup B) :
    rightOrthogonal P' Y = (leftOrthogonal P Y).map e.toAddMonoidHom
def toBidualIso : M ≅ PoitouTate.dual N (PoitouTate.dual N M)
theorem localization_coeffMap {A B : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)}
    [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : cohomology A n) :
    localization ι B v n (coeffMap f n x) =
      coeffMap ((Rep.resFunctor (localizationHom ι S v :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
          GaloisGroupUnramifiedOutside K Ω S)).map f) n (localization ι A v n x)
theorem localPairing_dual_toBidualIso (v : S) (x : cohomology (localModule ι M v) 1)
    (y : cohomology (localModule ι (PoitouTate.dual N M) v) 1) :
    localPairing ι N (PoitouTate.dual N M) v y
        (coeffAddEquiv ((Rep.resFunctor (localizationHom ι S v :
          Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)/
            (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) →*
              GaloisGroupUnramifiedOutside K Ω S)).mapIso (toBidualIso N M hS hM)) 1 x) =
      -localPairing ι N M v x y
def map (e : M₁ ≅ M₂) (L : LocalConditions ι M₁) : LocalConditions ι M₂
theorem selmerGroup_map (e : M₁ ≅ M₂) (L : LocalConditions ι M₁) :
    (L.map e).selmerGroup = L.selmerGroup.map (coeffAddEquiv e 1).toAddMonoidHom
theorem dual_dual (L : LocalConditions ι M) :
    (L.dual N).dual N = L.map (toBidualIso N M hS hM)
theorem selmerGroup_dual_dual (L : LocalConditions ι M) :
    ((L.dual N).dual N).selmerGroup =
      L.selmerGroup.map (coeffAddEquiv (toBidualIso N M hS hM) 1).toAddMonoidHom
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.rightOrthogonal_eq_map_leftOrthogonal : ∀ {A : Type u_1} {B : Type u_2} {C : Type u_3}
  [inst : AddCommGroup A] [inst_1 : AddCommGroup B] [inst_2 : AddCommGroup C]
  (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (P' : B →+ C →+ Langlands.ProfiniteCohomology.QZ) (e : A ≃+ C),
  (∀ (a : A) (b : B), (P' b) (e a) = -(P a) b) →
    ∀ (Y : AddSubgroup B),
      Langlands.ProfiniteCohomology.rightOrthogonal P' Y =
        AddSubgroup.map (AddEquiv.toAddMonoidHom e) (Langlands.ProfiniteCohomology.leftOrthogonal P Y)
@Langlands.GaloisCohomology.toBidualIso : {K Ω : Type u} →
  [inst : Field K] →
    [NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              (N : ℕ) →
                [NeZero N] →
                  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) →
                    [Finite ↑M] →
                      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                          ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S) →
                        (∀ (m : ↑M), N • m = 0) →
                          (M ≅
                            Langlands.GaloisCohomology.PoitouTate.dual N
                              (Langlands.GaloisCohomology.PoitouTate.dual N M))
@Langlands.GaloisCohomology.toBidualIso_hom : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (N : ℕ) [inst_5 : NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [inst_6 : Finite ↑M]
  (hS :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S)
  (hM : ∀ (m : ↑M), N • m = 0),
  CategoryTheory.Iso.hom (Langlands.GaloisCohomology.toBidualIso N M hS hM) =
    Langlands.ProfiniteCohomology.toDualDual (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
@Langlands.GaloisCohomology.localization_coeffMap : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep A] [inst_6 : Langlands.IsSmoothRep B] (f : A ⟶ B)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology A n)),
  (Langlands.GaloisCohomology.localization ι B v n)
      ((CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.coeffMap f n)) x) =
    (CategoryTheory.ConcreteCategory.hom
        (Langlands.ProfiniteCohomology.coeffMap
          (CategoryTheory.Functor.map (Rep.resFunctor ↑(Langlands.Galois.localizationHom ι S v)) f) n))
      ((Langlands.GaloisCohomology.localization ι A v n) x)
@Langlands.GaloisCohomology.isSmoothRep_dual_dual : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M],
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.PoitouTate.dual N (Langlands.GaloisCohomology.PoitouTate.dual N M))
@Langlands.GaloisCohomology.isSmoothRep_localModule_dual_dual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.localModule ι
      (Langlands.GaloisCohomology.PoitouTate.dual N (Langlands.GaloisCohomology.PoitouTate.dual N M)) v)
@Langlands.GaloisCohomology.isSmoothRep_realLocalModule_dual_dual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (w : NumberField.InfinitePlace K),
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.realLocalModule ι
      (Langlands.GaloisCohomology.PoitouTate.dual N (Langlands.GaloisCohomology.PoitouTate.dual N M)) w)
@Langlands.GaloisCohomology.localPairing_dual_toBidualIso : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_5 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M]
  (hS :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S)
  (hM : ∀ (m : ↑M), N • m = 0) (v : ↑S)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 1))
  (y :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑v) 1)),
  ((Langlands.GaloisCohomology.localPairing ι N (Langlands.GaloisCohomology.PoitouTate.dual N M) v) y)
      ((Langlands.GaloisCohomology.PoitouTate.coeffAddEquiv
          (CategoryTheory.Functor.mapIso (Rep.resFunctor ↑(Langlands.Galois.localizationHom ι S ↑v))
            (Langlands.GaloisCohomology.toBidualIso N M hS hM))
          1)
        x) =
    -((Langlands.GaloisCohomology.localPairing ι N M v) x) y
@Langlands.GaloisCohomology.realLocalPairing_dual_toBidualIso : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_5 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M]
  (hS :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S)
  (hM : ∀ (m : ↑M), N • m = 0) (w : { w // NumberField.InfinitePlace.IsReal w })
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1))
  (y :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑w) 1)),
  ((Langlands.GaloisCohomology.realLocalPairing ι N (Langlands.GaloisCohomology.PoitouTate.dual N M) w) y)
      ((Langlands.GaloisCohomology.PoitouTate.coeffAddEquiv
          (CategoryTheory.Functor.mapIso (Rep.resFunctor ↑(Langlands.Galois.realLocalizationHom ι S ↑w))
            (Langlands.GaloisCohomology.toBidualIso N M hS hM))
          1)
        x) =
    -((Langlands.GaloisCohomology.realLocalPairing ι N M w) x) y
@Langlands.GaloisCohomology.LocalConditions.map : {K Ω : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              {ι : Langlands.Galois.PlaceEmbeddings K Ω} →
                {M₁ M₂ : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} →
                  [inst_5 : Langlands.IsSmoothRep M₁] →
                    [inst_6 : Langlands.IsSmoothRep M₂] →
                      (M₁ ≅ M₂) →
                        Langlands.GaloisCohomology.LocalConditions ι M₁ →
                          Langlands.GaloisCohomology.LocalConditions ι M₂
@Langlands.GaloisCohomology.LocalConditions.selmerGroup_map : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω}
  {M₁ M₂ : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_5 : Langlands.IsSmoothRep M₁] [inst_6 : Langlands.IsSmoothRep M₂] (e : M₁ ≅ M₂)
  (L : Langlands.GaloisCohomology.LocalConditions ι M₁),
  Langlands.GaloisCohomology.LocalConditions.selmerGroup (Langlands.GaloisCohomology.LocalConditions.map e L) =
    AddSubgroup.map (AddEquiv.toAddMonoidHom (Langlands.GaloisCohomology.PoitouTate.coeffAddEquiv e 1))
      (Langlands.GaloisCohomology.LocalConditions.selmerGroup L)
@Langlands.GaloisCohomology.LocalConditions.dual_dual : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_5 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M]
  (hS :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S)
  (hM : ∀ (m : ↑M), N • m = 0) (L : Langlands.GaloisCohomology.LocalConditions ι M),
  Langlands.GaloisCohomology.LocalConditions.dual N (Langlands.GaloisCohomology.LocalConditions.dual N L) =
    Langlands.GaloisCohomology.LocalConditions.map (Langlands.GaloisCohomology.toBidualIso N M hS hM) L
@Langlands.GaloisCohomology.LocalConditions.selmerGroup_dual_dual : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [inst_5 : NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)}
  [inst_6 : Langlands.IsSmoothRep M] [inst_7 : Finite ↑M]
  (hS :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ↑N ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → v ∈ S)
  (hM : ∀ (m : ↑M), N • m = 0) (L : Langlands.GaloisCohomology.LocalConditions ι M),
  Langlands.GaloisCohomology.LocalConditions.selmerGroup
      (Langlands.GaloisCohomology.LocalConditions.dual N (Langlands.GaloisCohomology.LocalConditions.dual N L)) =
    AddSubgroup.map
      (AddEquiv.toAddMonoidHom
        (Langlands.GaloisCohomology.PoitouTate.coeffAddEquiv (Langlands.GaloisCohomology.toBidualIso N M hS hM) 1))
      (Langlands.GaloisCohomology.LocalConditions.selmerGroup L)
```

## Outline of the proofs

- Sign rule: `ptLocalPairing_dual_toDualDual` (of `Langlands.GaloisCohomology.CompactSupport.NineTerm`)
  at the places of `S` and the real places.
- `dual_dual`: `rightOrthogonal_eq_map_leftOrthogonal` and `leftOrthogonal_rightOrthogonal` for the
  perfect local pairings.
- `selmerGroup_map`: the localizations commute with the coefficient maps (`localization_coeffMap`,
  `realLocalization_coeffMap`), which are isomorphisms.

## Declarations

`rightOrthogonal_eq_map_leftOrthogonal`, `toBidualIso`, `toBidualIso_hom`, `localization_coeffMap`, `isSmoothRep_dual_dual`, `isSmoothRep_localModule_dual_dual`, `isSmoothRep_realLocalModule_dual_dual`, `localPairing_dual_toBidualIso`, `realLocalPairing_dual_toBidualIso`, `LocalConditions.map`, `LocalConditions.selmerGroup_map`, `LocalConditions.dual_dual`, `LocalConditions.selmerGroup_dual_dual`.

## References

No source is cited: the statements are formal consequences of the graded commutativity of the cup product and of local duality.
