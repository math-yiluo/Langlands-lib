# The trace of Poitou–Tate duality for `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/Trace.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)` and `ι : PlaceEmbeddings K Ω`. This file fixes the data in which the duality
theorems of Poitou and Tate for `G_S` are stated:

* the family of localization homomorphisms `G_{K_v} → G_S` at the places `v ∈ S` (`localFamily`)
  and at the real places (`realFamily`);
* the dualizing module `μ_N = μ_N(K_S)` (`dualizingModule`), for `N ≥ 1`;
* the local invariants `H²(K_v, μ_N) → ℚ/ℤ` (`invariantAt`), the image of the class in
  `H²(K_v, K̄_vˣ)` under the invariant of local class field theory, and the same at the real places
  (`realInvariantAt`, with the real invariant of the Brauer sequence);
* the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` (`trace`) on the cohomology with compact support in which degree
  `0` at the real places is Tate's `Ĥ⁰`. It is characterized by `trace_localToCompact`: on the image
  of `∏_{v ∈ S} H²(K_v, μ_N) × ∏_{w real} H²(K_w, μ_N)` it is the sum of the local invariants.

The trace exists because the sum of the local invariants vanishes on the localizations of a global
class (`sumInvariants_globalToLocal`): a class of `H²(G_S, μ_N)` maps to the Brauer group of `K`
with zero invariants outside `S`, and the sum of all invariants of a global Brauer class is zero
(the reciprocity law of the Brauer sequence, `localInvariant_finite_support_and_sum_eq_zero`). It is
chosen as an extension of this sum to `Ĥ_c³`; that the extension is unique follows from the
surjectivity of `∏ H²(·, μ_N) → Ĥ_c³(G_S, μ_N)`, a consequence of the duality theorem.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.brauerClass.{u} {K : Type u} (Ω : Type u) [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (N : ℕ) :
  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2) →+
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)
Langlands.GaloisCohomology.PoitouTate.brauerClass_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.PoitouTate.brauerClass Ω S N) x =
    (Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2)
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap
            (Langlands.GaloisCohomology.rootsOfUnityToUnits K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) N)
            2))
        x)
Langlands.GaloisCohomology.PoitouTate.brauerClass_eq_maximalSUnitsInflation.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.PoitouTate.brauerClass Ω S N) x =
    (Langlands.GaloisCohomology.maximalSUnitsInflation K Ω S 2)
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap
            (Langlands.GaloisCohomology.rootsOfUnityToSUnits S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) N)
            2))
        x)
Langlands.GaloisCohomology.PoitouTate.brauerLocalization_brauerClass.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.brauerLocalization ι v 2) ((Langlands.GaloisCohomology.PoitouTate.brauerClass Ω S N) x) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v) 2))
      ((Langlands.GaloisCohomology.localization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) v 2)
        x)
Langlands.GaloisCohomology.PoitouTate.brauerLocalization_brauerClass_eq_zero.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∉ S)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.brauerLocalization ι v 2) ((Langlands.GaloisCohomology.PoitouTate.brauerClass Ω S N) x) =
    0
Langlands.GaloisCohomology.PoitouTate.dualizingModule.{u} (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) :
  Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
Langlands.GaloisCohomology.PoitouTate.fintypeClosureGalois.{u} {K : Type u} [Field K] [NumberField K]
  (w : NumberField.InfinitePlace K) : Fintype Gal(AlgebraicClosure w.Completion/w.Completion)
Langlands.GaloisCohomology.PoitouTate.fintypeRealPlaces.{u} (K : Type u) [Field K] [NumberField K] :
  Fintype { w // w.IsReal }
Langlands.GaloisCohomology.PoitouTate.invariantAt.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) v)
        2) →+
    Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.invariantAt_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) v)
        2)) :
  (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N v) x =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers.symm
      ((Langlands.GaloisCohomology.finiteInvariant v)
        ((ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v)
              2))
          x))
Langlands.GaloisCohomology.PoitouTate.invariantAt_localization.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N v)
      ((Langlands.GaloisCohomology.localization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) v 2)
        x) =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers.symm
      ((Langlands.GaloisCohomology.localInvariant ι v) ((Langlands.GaloisCohomology.PoitouTate.brauerClass Ω S N) x))
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_dualizingModule.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) :
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_localModule_dualizingModule.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) v)
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_realLocalModule_dualizingModule.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) :
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) w)
Langlands.GaloisCohomology.PoitouTate.ker_localToCompact_le_ker_sumInvariants.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N] :
  (ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.ptTLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)).toAddMonoidHom.ker ≤
    (Langlands.GaloisCohomology.PoitouTate.sumInvariants ι S N).ker
Langlands.GaloisCohomology.PoitouTate.localFamily.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (v : ↑S) :
  Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) →ₜ*
    Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S
Langlands.GaloisCohomology.PoitouTate.nsmul_dualizingModule.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (ζ : ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)) : N • ζ = 0
Langlands.GaloisCohomology.PoitouTate.nsmul_traceQZ.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (z :
    ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3)) :
  N • (Langlands.GaloisCohomology.PoitouTate.traceQZ ι S N) z = 0
Langlands.GaloisCohomology.PoitouTate.realBrauerLocalization_brauerClass.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.realBrauerLocalization ι w 2)
      ((Langlands.GaloisCohomology.PoitouTate.brauerClass Ω S N) x) =
    (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityRealHom ι S N w) 2))
      ((Langlands.GaloisCohomology.realLocalization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) w
          2)
        x)
Langlands.GaloisCohomology.PoitouTate.realFamily.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (w : { w // w.IsReal }) :
  Gal(AlgebraicClosure (↑w).Completion/(↑w).Completion) →ₜ* Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S
Langlands.GaloisCohomology.PoitouTate.realInvariantAt.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) :
  ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) w)
        2) →+
    Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.realInvariantAt_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K)
  (x :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) w)
        2)) :
  (Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N w) x =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers.symm
      (Langlands.GaloisCohomology.realInvariant w
        ((ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityRealHom ι S N w)
              2))
          x))
Langlands.GaloisCohomology.PoitouTate.realInvariantAt_realLocalization.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N w)
      ((Langlands.GaloisCohomology.realLocalization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) w
          2)
        x) =
    Langlands.ProfiniteCohomology.QZ.toRationalModIntegers.symm
      (Langlands.GaloisCohomology.realLocalInvariant ι w ((Langlands.GaloisCohomology.PoitouTate.brauerClass Ω S N) x))
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) v ⟶
    Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom_hom_apply.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x : Additive ↥(rootsOfUnity N ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))) :
  ↑(Additive.toMul ((Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v)) x)) =
    (ι.finite v) ↑↑↑(Additive.toMul x)
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityRealHom.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) :
  Langlands.GaloisCohomology.realLocalModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) w ⟶
    Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityRealHom_hom_apply.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K)
  (x : Additive ↥(rootsOfUnity N ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))) :
  ↑(Additive.toMul ((Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityRealHom ι S N w)) x)) =
    (ι.infinite w) ↑↑↑(Additive.toMul x)
Langlands.GaloisCohomology.PoitouTate.sumInvariants.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) :
  Langlands.GaloisCohomology.ptTLocal (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2 →+
    Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.sumInvariants_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ)
  (ξ :
    Langlands.GaloisCohomology.ptTLocal (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2) :
  (Langlands.GaloisCohomology.PoitouTate.sumInvariants ι S N) ξ =
    ∑ v, (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) (ξ.1 v) +
      ∑ w, (Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w) (ξ.2 w)
Langlands.GaloisCohomology.PoitouTate.sumInvariants_globalToLocal.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  (Langlands.GaloisCohomology.PoitouTate.sumInvariants ι S N)
      ((ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.ptTGlobalToLocal (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2))
        x) =
    0
Langlands.GaloisCohomology.PoitouTate.sum_invariantAt_add_sum_realInvariantAt.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N] [Fintype ↑S]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  ∑ v,
        (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v)
          ((Langlands.GaloisCohomology.localization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
              (↑v) 2)
            x) +
      ∑ w,
        (Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w)
          ((Langlands.GaloisCohomology.realLocalization ι
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) (↑w) 2)
            x) =
    0
Langlands.GaloisCohomology.PoitouTate.trace.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N] :
  ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
    ZMod N
Langlands.GaloisCohomology.PoitouTate.traceQZ.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N] :
  ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
    Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.traceQZ_comp.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N] :
  (Langlands.GaloisCohomology.PoitouTate.traceQZ ι S N).comp
      (ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.ptTLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)).toAddMonoidHom =
    Langlands.GaloisCohomology.PoitouTate.sumInvariants ι S N
Langlands.GaloisCohomology.PoitouTate.trace_localToCompact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (ξ :
    Langlands.GaloisCohomology.ptTLocal (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2) :
  (Langlands.ProfiniteCohomology.zmodToQZ N)
      ((Langlands.GaloisCohomology.PoitouTate.trace ι S N)
        ((ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.ptTLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2))
          ξ)) =
    (Langlands.GaloisCohomology.PoitouTate.sumInvariants ι S N) ξ
```

Local Kummer theory at the places `v` (namespace `Langlands.GaloisCohomology`):
`rootsOfUnityLocalHom_injective` (`μ_N(K_S) → K̄_vˣ` is injective), `toMul_mem_rootsOfUnity_of_nsmul`,
`exists_rootsOfUnityLocalHom_eq` (an element of `K̄_vˣ` killed by `N` comes from `μ_N(K_S)` when `S`
contains the places above `N`); `localKummerSequence S ι N v`, the sequence
`0 → μ_N(K_S) → K̄_vˣ → K̄_vˣ → 0` (smoothness instances `isSmoothRep_localKummerSequence_X₁`, `_X₂`,
`_X₃`), short exact (`localKummerSequence_shortExact`); `injective_coeffMap_rootsOfUnityLocalHom_two`:
`H²(K_v, μ_N) → H²(K_v, K̄_vˣ)` is injective (Hilbert 90). The same sequence with the arguments in the
order `ι S N v` is `PoitouTate.localKummerSequence` of `Langlands.GaloisCohomology.Global.PoitouTate.EvenDuality`.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.toMul_mem_rootsOfUnity_of_nsmul.{u_1} (N : ℕ) {R : Type u_1} [CommMonoid R] (z : Additive Rˣ)
  (h : N • z = 0) : Additive.toMul z ∈ rootsOfUnity N R
Langlands.GaloisCohomology.rootsOfUnityLocalHom_injective.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Function.Injective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v))
Langlands.GaloisCohomology.exists_rootsOfUnityLocalHom_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (z : Additive (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) (hz : N • z = 0) :
  ∃ x, (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v)) x = z
Langlands.GaloisCohomology.localKummerSequence.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  CategoryTheory.ShortComplex
    (Rep.{u, u, u} (ULift.{u, 0} ℤ)
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
            v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
Langlands.GaloisCohomology.isSmoothRep_localKummerSequence_X₁.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.localKummerSequence S ι N v).X₁
Langlands.GaloisCohomology.isSmoothRep_localKummerSequence_X₂.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.localKummerSequence S ι N v).X₂
Langlands.GaloisCohomology.isSmoothRep_localKummerSequence_X₃.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.localKummerSequence S ι N v).X₃
Langlands.GaloisCohomology.localKummerSequence_shortExact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  (Langlands.GaloisCohomology.localKummerSequence S ι N v).ShortExact
Langlands.GaloisCohomology.injective_coeffMap_rootsOfUnityLocalHom_two.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Function.Injective
    ⇑(ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityLocalHom ι S N v) 2))
```

## Outline of the proofs

The local invariants on `H²(K_v, μ_N)` are the Library's `finiteInvariant` after `μ_N → K̄_vˣ`; the real ones `realInvariantQZ`. The sum formula `sum_invariantAt_add_sum_realInvariantAt` is the Brauer sequence of the Library (`localInvariant_finite_support_and_sum_eq_zero`) applied to the Brauer class of `x` (`brauerClass`, which factors through the `S`-units: `brauerClass_eq_maximalSUnitsInflation`, so only the places of `S` and the real places contribute). Hence the sum of the invariants vanishes on the kernel of `∏ H²(·, μ_N) → Ĥ_c³(G_S, μ_N)` and extends (`QZ.exists_comp_eq_of_ker_le`) to the trace.

## Declarations

`fintypeRealPlaces`, `fintypeClosureGalois`, `localFamily`, `realFamily`, `dualizingModule`, `isSmoothRep_dualizingModule`, `nsmul_dualizingModule`, `isSmoothRep_localModule_dualizingModule`, `isSmoothRep_realLocalModule_dualizingModule`, `rootsOfUnityLocalHom`, `rootsOfUnityLocalHom_hom_apply`, `rootsOfUnityRealHom`, `rootsOfUnityRealHom_hom_apply`, `invariantAt`, `invariantAt_apply`, `realInvariantAt`, `realInvariantAt_apply`, `brauerClass`, `brauerClass_apply`, `brauerClass_eq_maximalSUnitsInflation`, `brauerLocalization_brauerClass`, `realBrauerLocalization_brauerClass`, `brauerLocalization_brauerClass_eq_zero`, `invariantAt_localization`, `realInvariantAt_realLocalization`, `sum_invariantAt_add_sum_realInvariantAt`, `sumInvariants`, `sumInvariants_apply`, `sumInvariants_globalToLocal`, `ker_localToCompact_le_ker_sumInvariants`, `traceQZ`, `traceQZ_comp`, `nsmul_traceQZ`, `trace`, `trace_localToCompact`, `toMul_mem_rootsOfUnity_of_nsmul`, `rootsOfUnityLocalHom_injective`, `exists_rootsOfUnityLocalHom_eq`, `localKummerSequence`, `isSmoothRep_localKummerSequence_X₁`, `isSmoothRep_localKummerSequence_X₂`, `isSmoothRep_localKummerSequence_X₃`, `localKummerSequence_shortExact`, `injective_coeffMap_rootsOfUnityLocalHom_two`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/PoitouTate/RealTrace.lean` and `RealTraceMap.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The source's trace through its own class field theory is replaced by the Library's Brauer sequence.

The local Kummer theory (`localKummerSequence` … `injective_coeffMap_rootsOfUnityLocalHom_two`) is
ported from `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/KummerSha.lean` (lines
1–155; `injective_coeffMap_rootsOfUnityLocalHom_two` is the source's
`cohomologyMap_gsRootsLocalUnitsMor_injective`) and `GlobalEulerCharacteristic/ShaCount.lean` (lines
60–98) of the repository `leanprover-community/riemann-hypothesis`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
