# The local pairings of the Poitou–Tate sequence

`Langlands/GaloisCohomology/Global/PoitouTate/LocalPairings.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

For a place `w` with local Galois group `Gal(L/F)` (`L` an algebraic closure of the completion `F`),
a homomorphism `φ : Gal(L/F) →ₜ* G_S` and an injective coefficient map `j : μ_N(K_S) → Lˣ`, the
dual `M' = Hom(M, μ_N)` of a `G_S`-module `M` killed by `N`, restricted to `Gal(L/F)`, is the Cartier
dual `Hom(M, Lˣ)` of `M`: post-composition with `j` is an isomorphism (`dualToCartier`,
`bijective_dualToCartier`), and the local pairing of the Poitou–Tate sequence,
`Hʳ(F, M) × Hˢ(F, M') → H²(F, μ_N) → ℚ/ℤ`, is the cup product with the Cartier pairing
`M ⊗ Hom(M, Lˣ) → Lˣ` followed by the invariant (`cupPairing_dualToCartier`).

At the real places this identifies the local pairings with those of `realLocalDuality`, which gives
the surjectivity statements the abstract nine-term sequence needs
(`surjective_realPairing_zero`, `exists_realPairing_two`). At the finite places it reduces the same
statements to local Tate duality for the completions (`localTateDualityStatement` and
`surjective_localPairing` of `Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.bijective_dualToCartier.{u} {F L : Type u} [Field F] [Field L] [Algebra F L]
  {G : Type u} [Group G] [TopologicalSpace G] (φ : Gal(L/F) →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  (j : Rep.res (↑φ) D ⟶ Langlands.GaloisCohomology.unitsModule F L) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) {N : ℕ}
  [NeZero N] (hL : Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule F L N) ≃+ ZMod N))
  (hD : Nonempty (↑D ≃+ ZMod N)) (hj : Function.Injective ⇑(Rep.Hom.hom j)) [Finite ↑M] (hM : ∀ (m : ↑M), N • m = 0) :
  Function.Bijective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.dualToCartier φ D j M))
Langlands.GaloisCohomology.PoitouTate.coeffAddEquiv.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] (e : A ≅ B)
  (m : ℕ) : ↑(Langlands.ProfiniteCohomology.cohomology A m) ≃+ ↑(Langlands.ProfiniteCohomology.cohomology B m)
Langlands.GaloisCohomology.PoitouTate.coeffAddEquiv_apply.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] (e : A ≅ B)
  (m : ℕ) (x : ↑(Langlands.ProfiniteCohomology.cohomology A m)) :
  (Langlands.GaloisCohomology.PoitouTate.coeffAddEquiv e m) x =
    (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap e.hom m)) x
Langlands.GaloisCohomology.PoitouTate.coeffMap_normClass.{u} {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [Fintype F] {B B' : Rep.{u, u, u} k F} [Langlands.IsSmoothRep B] [Langlands.IsSmoothRep B']
  (f : B ⟶ B') (m : ↑B) :
  (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap f 0)) (Langlands.GaloisCohomology.normClass B m) =
    Langlands.GaloisCohomology.normClass B' ((Rep.Hom.hom f) m)
Langlands.GaloisCohomology.PoitouTate.cupPairing_dualToCartier.{u} {F L : Type u} [Field F] [Field L] [Algebra F L]
  {G : Type u} [Group G] [TopologicalSpace G] (φ : Gal(L/F) →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  (j : Rep.res (↑φ) D ⟶ Langlands.GaloisCohomology.unitsModule F L) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  [IsTopologicalGroup G] [Algebra.IsIntegral F L] [Langlands.IsSmoothRep D] [Langlands.IsSmoothRep M] [Finite ↑M]
  [Langlands.IsSmoothRep (Langlands.GaloisCohomology.cartierDual F L (Rep.res (↑φ) M))] {r s : ℕ} (h : r + s = 2)
  (ξ : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑φ) M) r))
  (η : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M)) s)) :
  ((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.cartierPairing F L (Rep.res (↑φ) M)) h) ξ)
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.dualToCartier φ D j M) s))
        η) =
    (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap j 2))
      (((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.PoitouTate.resEval φ D M) h) ξ) η)
Langlands.GaloisCohomology.PoitouTate.dualToCartier.{u} {F L : Type u} [Field F] [Field L] [Algebra F L] {G : Type u}
  [Group G] [TopologicalSpace G] (φ : Gal(L/F) →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  (j : Rep.res (↑φ) D ⟶ Langlands.GaloisCohomology.unitsModule F L) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) :
  Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M) ⟶ Langlands.GaloisCohomology.cartierDual F L (Rep.res (↑φ) M)
Langlands.GaloisCohomology.PoitouTate.dualToCartier_hom_apply.{u} {F L : Type u} [Field F] [Field L] [Algebra F L]
  {G : Type u} [Group G] [TopologicalSpace G] (φ : Gal(L/F) →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  (j : Rep.res (↑φ) D ⟶ Langlands.GaloisCohomology.unitsModule F L) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  (f : ↑M →ₗ[ULift.{u, 0} ℤ] ↑D) (m : ↑M) :
  ((Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.dualToCartier φ D j M)) f) m = (Rep.Hom.hom j) (f m)
Langlands.GaloisCohomology.PoitouTate.exists_orderTwo_pairing_two.{u} {F L : Type u} [Field F] [Field L] [Algebra F L]
  [DiscreteTopology Gal(L/F)] [Fintype Gal(L/F)] [Algebra.IsIntegral F L] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (φ : Gal(L/F) →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D]
  (j : Rep.res (↑φ) D ⟶ Langlands.GaloisCohomology.unitsModule F L) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  [Langlands.IsSmoothRep M] [Finite ↑M]
  (invariant :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule F L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/F)} (hG : ∀ (g : Gal(L/F)), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hinv :
    ∀ (t : ↑(Langlands.GaloisCohomology.unitsModule F L))
      (ht : ((Langlands.GaloisCohomology.unitsModule F L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          invariant
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule F L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule F L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2))
  (hconj :
    ∀ (ζ : ↑(Langlands.GaloisCohomology.unitsModule F L)),
      (∃ k, 0 < k ∧ k • ζ = 0) → ((Langlands.GaloisCohomology.unitsModule F L).ρ c) ζ = -ζ)
  (hroots : ∀ (k : ℕ), 0 < k → Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule F L k) ≃+ ZMod k)) {N : ℕ}
  [NeZero N] (hD : Nonempty (↑D ≃+ ZMod N)) (hj : Function.Injective ⇑(Rep.Hom.hom j)) (hM : ∀ (m : ↑M), N • m = 0)
  (χ :
    ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M)) 0) →+
      Langlands.ProfiniteCohomology.QZ)
  (hχ :
    ∀ x ∈ Langlands.GaloisCohomology.normClasses (Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M)), χ x = 0) :
  ∃ ξ,
    ∀ (η : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M)) 0)),
      invariant
          ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap j 2))
            (((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.PoitouTate.resEval φ D M) ⋯) ξ)
              η)) =
        χ η
Langlands.GaloisCohomology.PoitouTate.exists_orderTwo_pairing_zero.{u} {F L : Type u} [Field F] [Field L] [Algebra F L]
  [DiscreteTopology Gal(L/F)] [Fintype Gal(L/F)] [Algebra.IsIntegral F L] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (φ : Gal(L/F) →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D]
  (j : Rep.res (↑φ) D ⟶ Langlands.GaloisCohomology.unitsModule F L) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  [Langlands.IsSmoothRep M] [Finite ↑M]
  (invariant :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule F L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/F)} (hG : ∀ (g : Gal(L/F)), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hinv :
    ∀ (t : ↑(Langlands.GaloisCohomology.unitsModule F L))
      (ht : ((Langlands.GaloisCohomology.unitsModule F L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          invariant
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule F L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule F L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2))
  (hconj :
    ∀ (ζ : ↑(Langlands.GaloisCohomology.unitsModule F L)),
      (∃ k, 0 < k ∧ k • ζ = 0) → ((Langlands.GaloisCohomology.unitsModule F L).ρ c) ζ = -ζ)
  (hroots : ∀ (k : ℕ), 0 < k → Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule F L k) ≃+ ZMod k)) {N : ℕ}
  [NeZero N] (hD : Nonempty (↑D ≃+ ZMod N)) (hj : Function.Injective ⇑(Rep.Hom.hom j)) (hM : ∀ (m : ↑M), N • m = 0)
  (χ :
    ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M)) 2) →+
      Langlands.ProfiniteCohomology.QZ) :
  ∃ ξ,
    ∀ (η : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M)) 2)),
      invariant
          ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap j 2))
            (((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.PoitouTate.resEval φ D M) ⋯) ξ)
              η)) =
        χ η
Langlands.GaloisCohomology.PoitouTate.exists_realPairing_two.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Nonempty (↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) ≃+ ZMod N))
  (hM : ∀ (m : ↑M), N • m = 0) (w : { w // w.IsReal })
  (χ :
    ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.realLocalModule ι
            (Langlands.ProfiniteCohomology.dualRep (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M)
            ↑w)
          0) →+
      Langlands.ProfiniteCohomology.QZ)
  (hχ :
    ∀
      x ∈
        Langlands.GaloisCohomology.normClasses
          (Langlands.GaloisCohomology.realLocalModule ι
            (Langlands.ProfiniteCohomology.dualRep (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M)
            ↑w),
      χ x = 0) :
  ∃ ξ,
    (Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
          (fun w => Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w) w ⋯)
        ξ =
      χ
Langlands.GaloisCohomology.PoitouTate.finite_res.{u} {k G H : Type u} [CommRing k] [Monoid G] [Monoid H] (φ : H →* G)
  (M : Rep.{u, u, u} k G) [Finite ↑M] : Finite ↑(Rep.res φ M)
Langlands.GaloisCohomology.PoitouTate.injective_rootsOfUnityLocalHom.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Function.Injective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v))
Langlands.GaloisCohomology.PoitouTate.injective_rootsOfUnityRealHom.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) :
  Function.Injective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityRealHom ι S N w))
Langlands.GaloisCohomology.PoitouTate.resEval.{u} {F L : Type u} [Field F] [Field L] [Algebra F L] {G : Type u}
  [Group G] [TopologicalSpace G] (φ : Gal(L/F) →ₜ* G) (D M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) :
  CategoryTheory.MonoidalCategoryStruct.tensorObj (Rep.res (↑φ) M)
      (Rep.res (↑φ) (Langlands.ProfiniteCohomology.dualRep D M)) ⟶
    Rep.res (↑φ) D
Langlands.GaloisCohomology.PoitouTate.surjective_realPairing_zero.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Nonempty (↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) ≃+ ZMod N))
  (hM : ∀ (m : ↑M), N • m = 0) (w : { w // w.IsReal }) :
  Function.Surjective
    ⇑(Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
        (fun w => Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w) w ⋯)
Langlands.GaloisCohomology.PoitouTate.tensorHom_dualToCartier_cartierPairing.{u} {F L : Type u} [Field F] [Field L]
  [Algebra F L] {G : Type u} [Group G] [TopologicalSpace G] (φ : Gal(L/F) →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  (j : Rep.res (↑φ) D ⟶ Langlands.GaloisCohomology.unitsModule F L) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) :
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id (Rep.res (↑φ) M))
        (Langlands.GaloisCohomology.PoitouTate.dualToCartier φ D j M))
      (Langlands.GaloisCohomology.cartierPairing F L (Rep.res (↑φ) M)) =
    CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.PoitouTate.resEval φ D M) j
```

The pairings in degrees `1 + 1` (namespace `Langlands.GaloisCohomology`): `localPairing ι N M v` at a
place `v ∈ S` and `realLocalPairing ι N M w` at a real place `w` (`localPairing_eq`,
`realLocalPairing_eq`: they are `ptLocalPairing` with `invariantAt`, `realInvariantAt`), and their sum
`localTermPairing ι N M` on `P¹(M) × P¹(M')` (`localTermPairing_apply`); **`locDual` in degrees
`1 + 1`** is the sum of the local pairings with the localizations of global classes of `M'`
(`locDual_one_apply`).

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.localPairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (v : ↑S) :
  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 1) →+
    ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑v) 1) →+
      Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.localPairing_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (v : ↑S) :
  Langlands.GaloisCohomology.localPairing ι N M v =
    Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
      (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) v ⋯
Langlands.GaloisCohomology.realLocalPairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (w : { w // w.IsReal }) :
  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 1) →+
    ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑w) 1) →+
      Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.realLocalPairing_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (w : { w // w.IsReal }) :
  Langlands.GaloisCohomology.realLocalPairing ι N M w =
    Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
      (fun w => Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w) w ⋯
Langlands.GaloisCohomology.localTermPairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] :
  Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1 →+
    Langlands.GaloisCohomology.PoitouTate.LocalTerm ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 1 →+
      Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.localTermPairing_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1)
  (η : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 1) :
  ((Langlands.GaloisCohomology.localTermPairing ι N M) ξ) η =
    ∑ v, ((Langlands.GaloisCohomology.localPairing ι N M v) (ξ.1 v)) (η.1 v) +
      ∑ w, ((Langlands.GaloisCohomology.realLocalPairing ι N M w) (ξ.2 w)) (η.2 w)
Langlands.GaloisCohomology.locDual_one_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 1)) :
  ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) y =
    ((Langlands.GaloisCohomology.localTermPairing ι N M) ξ)
      ((Langlands.GaloisCohomology.PoitouTate.loc ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 1) y)
```

## Outline of the proofs

`dualToCartier` is the adjoint of the evaluation followed by `μ_N → K̄_vˣ` (`Rep.tensorHomEquiv`); it is injective since `μ_N → K̄_vˣ` is, and bijective by counting (`card_dualRep_le`, `bijective_toDualDual`). At the real places the cohomology of `Gal(ℂ/ℝ)` is computed by `orderTwoLocalDuality` and `realLocalDuality`.

## Declarations

`coeffMap_normClass`, `finite_res`, `resEval`, `dualToCartier`, `dualToCartier_hom_apply`, `bijective_dualToCartier`, `tensorHom_dualToCartier_cartierPairing`, `cupPairing_dualToCartier`, `coeffAddEquiv`, `coeffAddEquiv_apply`, `exists_orderTwo_pairing_zero`, `exists_orderTwo_pairing_two`, `injective_rootsOfUnityLocalHom`, `injective_rootsOfUnityRealHom`, `surjective_realPairing_zero`, `exists_realPairing_two`, `localPairing`, `localPairing_eq`, `realLocalPairing`, `realLocalPairing_eq`, `localTermPairing`, `localTermPairing_apply`, `locDual_one_apply`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
