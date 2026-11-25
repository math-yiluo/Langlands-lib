# Local Tate duality at the places of `S`

`Langlands/GaloisCohomology/Global/PoitouTate/LocalDuality.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

For a finite place `v` of a number field `K`, the local Tate pairing
`Hʳ(K_v, M) × Hˢ(K_v, M^D) → H²(K_v, K̄_vˣ) → ℚ/ℤ` (`r + s = 2`, `M^D = Hom(M, K̄_vˣ)` the Cartier
dual, the last map the invariant of local class field theory `finiteInvariant`) is `localTatePairing`.
`LocalTateDualityStatement` says that it is perfect on both sides for every finite smooth module, for
number fields in a given universe; it holds in every universe (`localTateDualityStatement`), by local
Tate duality of the Library (`Langlands.GaloisCohomology.Local.tatePairing_bijective` and
`tatePairing_flip_bijective`) for the local field `v.adicCompletion K`.

From it, through `dualToCartier`, the local pairings of the Poitou–Tate sequence at the places of `S`
are perfect (`surjective_localPairing`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.LocalTateDualityStatement.{u} : Prop
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_cartierDual_localModule.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.cartierDual (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (Langlands.GaloisCohomology.localModule ι M v))
Langlands.GaloisCohomology.PoitouTate.localTateDualityStatement.{u} :
  Langlands.GaloisCohomology.PoitouTate.LocalTateDualityStatement
Langlands.GaloisCohomology.PoitouTate.localTatePairing.{u} {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (M :
    Rep.{u, u, u} (ULift.{u, 0} ℤ)
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
            v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  [Langlands.IsSmoothRep M] [Finite ↑M] {r s : ℕ} (h : r + s = 2) :
  ↑(Langlands.ProfiniteCohomology.cohomology M r) →+
    ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.cartierDual (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) M)
          s) →+
      Langlands.ClassFieldTheory.Local.RationalModIntegers
Langlands.GaloisCohomology.PoitouTate.localTatePairing_apply.{u} {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (M :
    Rep.{u, u, u} (ULift.{u, 0} ℤ)
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
            v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  [Langlands.IsSmoothRep M] [Finite ↑M] {r s : ℕ} (h : r + s = 2) (x : ↑(Langlands.ProfiniteCohomology.cohomology M r))
  (y :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.cartierDual (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) M)
        s)) :
  ((Langlands.GaloisCohomology.PoitouTate.localTatePairing v M h) x) y =
    (Langlands.GaloisCohomology.finiteInvariant v)
      (((Langlands.ProfiniteCohomology.cupPairing
            (Langlands.GaloisCohomology.cartierPairing (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
              (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) M)
            h)
          x)
        y)
Langlands.GaloisCohomology.PoitouTate.ptLocalPairing_eq_localTatePairing.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (v : ↑S) {r s : ℕ} (h : r + s = 2)
  (ξ : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) r))
  (η :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι
          (Langlands.ProfiniteCohomology.dualRep (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M) ↑v)
        s)) :
  ((Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
          (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) v h)
        ξ)
      η =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers.symm
      (((Langlands.GaloisCohomology.PoitouTate.localTatePairing (↑v) (Langlands.GaloisCohomology.localModule ι M ↑v) h)
          ξ)
        ((ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.coeffMap
              (Langlands.GaloisCohomology.PoitouTate.dualToCartier (Langlands.Galois.localizationHom ι S ↑v)
                (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
                (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N ↑v) M)
              s))
          η))
Langlands.GaloisCohomology.PoitouTate.surjective_localPairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Nonempty (↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) ≃+ ZMod N))
  (hM : ∀ (m : ↑M), N • m = 0) (v : ↑S) {r s : ℕ} (h : r + s = 2) :
  Function.Surjective
    ⇑(Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
        (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) v h)
```

Comparison with Tate's pairing (namespace `Langlands.GaloisCohomology`): `toCartierDualLocal`, the map
`Hom(B, μ_N) → B^D` (Cartier dual) at `v` by postcomposition with `μ_N(K_S) → K̄_vˣ`
(`toCartierDualLocal_hom_apply`, instance `isSmoothRep_cartierDual_localModule`), bijective on `H⁰`
(`bijective_coeffMap_toCartierDualLocal_zero`); the local pairing of the Poitou–Tate sequence is the
Tate pairing through it (`ptLocalEval_comp_rootsOfUnityLocalHom`, `ptLocalPairing_eq_tatePairing`), and is
perfect in degrees `(2, 0)` (`surjective_ptLocalPairing_two`, `bijective_ptLocalPairing_two`), by
`Langlands.GaloisCohomology.Local.tatePairing_bijective`.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.toCartierDualLocal.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dual N B) v ⟶
    Langlands.GaloisCohomology.cartierDual (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (Langlands.GaloisCohomology.localModule ι B v)
Langlands.GaloisCohomology.toCartierDualLocal_hom_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (f : ↑B →ₗ[ULift.{u, 0} ℤ] ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)) (m : ↑B) :
  ((Rep.Hom.hom (Langlands.GaloisCohomology.toCartierDualLocal ι N B v)) f) m =
    (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v)) (f m)
Langlands.GaloisCohomology.isSmoothRep_cartierDual_localModule.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep B]
  [Finite ↑B] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.cartierDual (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (Langlands.GaloisCohomology.localModule ι B v))
Langlands.GaloisCohomology.bijective_coeffMap_toCartierDualLocal_zero.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  [Langlands.IsSmoothRep B] [Finite ↑B] (hB : ∀ (b : ↑B), N • b = 0)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Function.Bijective
    ⇑(ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.toCartierDualLocal ι N B v) 0))
Langlands.GaloisCohomology.ptLocalEval_comp_rootsOfUnityLocalHom.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Finite ↑S] (v : ↑S) :
  CategoryTheory.CategoryStruct.comp
      (Langlands.GaloisCohomology.ptLocalEval (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) B v)
      (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N ↑v) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom
        (CategoryTheory.CategoryStruct.id (Langlands.GaloisCohomology.localModule ι B ↑v))
        (Langlands.GaloisCohomology.toCartierDualLocal ι N B ↑v))
      (Langlands.GaloisCohomology.cartierPairing (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
        (Langlands.GaloisCohomology.localModule ι B ↑v))
Langlands.GaloisCohomology.ptLocalPairing_eq_tatePairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Finite ↑S]
  [Langlands.IsSmoothRep B] [Finite ↑B] (v : ↑S) {r s : ℕ} (h : r + s = 2)
  (ξ : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι B ↑v) r))
  (y :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dual N B) ↑v) s)) :
  ((Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) B
          (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) v h)
        ξ)
      y =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers.symm
      (((Langlands.GaloisCohomology.Local.tatePairing (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
            (Langlands.GaloisCohomology.localModule ι B ↑v) h)
          ξ)
        ((ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.toCartierDualLocal ι N B ↑v) s))
          y))
Langlands.GaloisCohomology.surjective_ptLocalPairing_two.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) [Finite ↑S]
  [Langlands.IsSmoothRep B] [Finite ↑B] (hB : ∀ (b : ↑B), N • b = 0) (v : ↑S) :
  Function.Surjective
    ⇑(Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) B
        (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) v ⋯)
Langlands.GaloisCohomology.bijective_ptLocalPairing_two.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (B : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) [Finite ↑S]
  [Langlands.IsSmoothRep B] [Finite ↑B] (hB : ∀ (b : ↑B), N • b = 0) (v : ↑S) :
  Function.Bijective
    ⇑(Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) B
        (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) v ⋯)
```

## Outline of the proofs

`localTateDualityStatement` is the Library's local Tate duality `Local.tatePairing_bijective`, `Local.tatePairing_flip_bijective` for the local field `v.adicCompletion K` (with `FiniteCompletion.valuativeRel` and `isNonarchimedeanLocalField`); the comparison with the pairing of the abstract layer goes through `dualToCartier` (`cupPairing_dualToCartier`).

## Declarations

`localTatePairing`, `localTatePairing_apply`, `LocalTateDualityStatement`, `localTateDualityStatement`, `isSmoothRep_cartierDual_localModule`, `ptLocalPairing_eq_localTatePairing`, `surjective_localPairing`, `toCartierDualLocal`, `toCartierDualLocal_hom_apply`, `isSmoothRep_cartierDual_localModule`, `bijective_coeffMap_toCartierDualLocal_zero`, `ptLocalEval_comp_rootsOfUnityLocalHom`, `ptLocalPairing_eq_tatePairing`, `surjective_ptLocalPairing_two`, `bijective_ptLocalPairing_two`.

## Source and licence

The comparison with Tate's pairing (`toCartierDualLocal` … `bijective_ptLocalPairing_two`) comes with the
text that the licence record lists for `GlobalEulerCharacteristic/ShaCount.lean` lines 60–98 of the
repository `leanprover-community/riemann-hypothesis`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The rest of the file contains no text of
the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
