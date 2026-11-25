# The Kummer sequence of the `S`-units with compact support

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Kummer.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal`.

Let `K` be a number field, `Ω` a separable closure, `ι : PlaceEmbeddings K Ω`, `S` a finite set of
finite places of `K`, `n ≥ 1` with the places above `n` in `S`, and `E = 𝒪_{K_S,S}ˣ` the `S`-units
of `K_S`. At a finite place `v` the embedding `ι.finite v` gives the coefficient maps
`K_Sˣ → K̄_vˣ` (`maximalUnitsLocalHom`) and `E → K̄_vˣ` (`sUnitsLocalHom`), morphisms of modules of
the local Galois group `G_{K_v}` acting through `localizationHom ι S v`. The Kummer sequence
`0 → μ_n → E → E → 0` of `G_S` (`sUnitsKummerSequence`) maps to the local Kummer sequences
`0 → μ_n → K̄_vˣ → K̄_vˣ → 0` at the places of `S` (`kummerLocalMap`: the identity on `μ_n`, which is
restricted to `G_{K_v}`, and `sUnitsLocalHom` on the units). Its connecting map with compact
support (`compactSupportδ`) is

  `kummerCompactδ : H_c¹(G_S, E; (K̄_vˣ)_{v ∈ S}) → H_c²(G_S, μ_n)`,

the target being `compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2`, the
group in which `RootsOfUnityPairingStatement` is stated. The domain is `unitsCompact ι S 1`.

**Surjectivity** (`surjective_kummerCompactδ`). For `n` a prime power, the places above `n` in `S`,
and `n` odd or `K` totally complex, `kummerCompactδ` is surjective. Its cokernel is the image of
`H_c²(G_S, μ_n) → H_c²(G_S, E)`, which is zero (`compactSupportMap_rootsOfUnityToSUnits_eq_zero`):
the image of a class of `H_c²(G_S, μ_n)` in `H²(G_S, μ_n)` vanishes at the places of `S`, so its
image in `H²(G_S, E)` is zero (`coeffMap_rootsOfUnityToSUnits_eq_zero`), and the local groups
`H¹(K_v, K̄_vˣ)` vanish (Hilbert 90).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.GaloisCohomology.localModule ι
      (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) v ⟶
    Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom_hom_apply.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x : Additive (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ) :
  ↑(Additive.toMul ((Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.maximalUnitsLocalHom ι S v)) x)) =
    (ι.finite v) ↑↑(Additive.toMul x)
Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) v ⟶
    Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom_hom_apply.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (x : Additive ↥(Langlands.GaloisCohomology.maximalSUnits K Ω S)) :
  ↑(Additive.toMul ((Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S v)) x)) =
    (ι.finite v) ↑↑↑(Additive.toMul x)
Langlands.GaloisCohomology.PoitouTate.Internal.isSmoothRep_localKummerSequence_X₁.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S n v).X₁
Langlands.GaloisCohomology.PoitouTate.Internal.isSmoothRep_localKummerSequence_X₂.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S n v).X₂
Langlands.GaloisCohomology.PoitouTate.Internal.isSmoothRep_localKummerSequence_X₃.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S n v).X₃
Langlands.GaloisCohomology.PoitouTate.Internal.kummerLocalMap.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] (v : ↑S) :
  (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n).map
      (Rep.resFunctor ↑(Langlands.GaloisCohomology.PoitouTate.localFamily ι S v)) ⟶
    Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S n ↑v
Langlands.GaloisCohomology.PoitouTate.Internal.kummerLocalMap_τ₁.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] (v : ↑S) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.kummerLocalMap ι S n v).τ₁ =
    CategoryTheory.CategoryStruct.id
      (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) ↑v)
Langlands.GaloisCohomology.PoitouTate.Internal.kummerLocalMap_τ₃.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) [NeZero n] (v : ↑S) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.kummerLocalMap ι S n v).τ₃ =
    Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v
Langlands.GaloisCohomology.PoitouTate.Internal.natCast_notMem_of_notMem.{u} {K : Type u} [Field K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (n : ℕ)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : v ∉ S → ↑n ∉ v.asIdeal
Langlands.GaloisCohomology.PoitouTate.Internal.unitsCompact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (m : ℕ) : ModuleCat (ULift.{u, 0} ℤ)
Langlands.GaloisCohomology.PoitouTate.Internal.kummerCompactδ.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (n : ℕ) [NeZero n]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) :
  Langlands.GaloisCohomology.PoitouTate.Internal.unitsCompact ι S 1 ⟶
    Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2
Langlands.GaloisCohomology.PoitouTate.Internal.compactSupportMap_compactToGlobal.{u} {k G : Type u} [CommRing k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ι' : Type u} {H : ι' → Type u} [(v : ι') → Group (H v)]
  [(v : ι') → TopologicalSpace (H v)] [∀ (v : ι'), IsTopologicalGroup (H v)] (φ : (v : ι') → H v →ₜ* G)
  {A B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B]
  {Aᵥ Bᵥ : (v : ι') → Rep.{u, u, u} k (H v)} [∀ (v : ι'), Langlands.IsSmoothRep (Aᵥ v)]
  [∀ (v : ι'), Langlands.IsSmoothRep (Bᵥ v)] {a : (v : ι') → Rep.res (↑(φ v)) A ⟶ Aᵥ v}
  {b : (v : ι') → Rep.res (↑(φ v)) B ⟶ Bᵥ v} (g : A ⟶ B) (gᵥ : (v : ι') → Aᵥ v ⟶ Bᵥ v)
  (hg :
    ∀ (v : ι'),
      CategoryTheory.CategoryStruct.comp (a v) (gᵥ v) =
        CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map g) (b v))
  (m : ℕ) :
  CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.compactSupportMap φ g gᵥ hg m)
      (Langlands.GaloisCohomology.compactToGlobal φ B Bᵥ b m) =
    CategoryTheory.CategoryStruct.comp (Langlands.GaloisCohomology.compactToGlobal φ A Aᵥ a m)
      (Langlands.ProfiniteCohomology.coeffMap g m)
Langlands.GaloisCohomology.PoitouTate.Internal.eq_zero_realBrauerGroup_of_nsmul.{u} {K : Type u} [Field K]
  [NumberField K] {n : ℕ} (hK : Odd n ∨ NumberField.IsTotallyComplex K) (w : NumberField.InfinitePlace K)
  (b : Langlands.GaloisCohomology.RealBrauerGroup w) (hb : n • b = 0) : b = 0
Langlands.GaloisCohomology.PoitouTate.Internal.coeffMap_rootsOfUnityToSUnits_eq_zero.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [NeZero n] (hn : IsPrimePow n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2))
  (hx :
    x ∈
      Langlands.GaloisCohomology.ptSha (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2) :
  (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap
          (Langlands.GaloisCohomology.rootsOfUnityToSUnits S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n) 2))
      x =
    0
Langlands.GaloisCohomology.PoitouTate.Internal.subsingleton_cohomology_one_localUnits.{u} {K : Type u} [Field K]
  [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Subsingleton
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
        1)
Langlands.GaloisCohomology.PoitouTate.Internal.compactSupportMap_rootsOfUnityToSUnits_eq_zero.{u} {K Ω : Type u}
  [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [NeZero n] (hn : IsPrimePow n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (y :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S n) 2)) :
  (ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.compactSupportMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.sUnitsKummerSequence S (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n).f
          (fun v => (Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S n ↑v).f) ⋯ 2))
      y =
    0
Langlands.GaloisCohomology.PoitouTate.Internal.surjective_kummerCompactδ.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} [NeZero n] (hn : IsPrimePow n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K) :
  Function.Surjective ⇑(ModuleCat.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.kummerCompactδ ι n hS))
```

## Outline of the proofs

`coeffMap_rootsOfUnityToSUnits_eq_zero`: for `n = ℓᵏ`, the image `y ∈ H²(G_S, E)` of a class `x` of
`H²(G_S, μ_n)` that vanishes at the places of `S` is killed by `ℓᵏ` and its Brauer class
(`maximalSUnitsInflation`) is zero: at the places of `S` it is the image of the localization of `x`,
outside `S` the Brauer class of a class of `H²(G_S, μ_n)` is locally trivial
(`brauerLocalization_brauerClass_eq_zero`), and at the infinite places it is killed by `n` and by
`2` (`eq_zero_realBrauerGroup_of_nsmul`; for `K` totally complex there are no real places), so it is
zero by the Brauer–Hasse–Noether injectivity `eq_zero_of_brauerLocalization_eq_zero'`; then
`eq_zero_of_maximalSUnitsInflation_eq_zero` (injectivity of `H²(G_S, E)(ℓ) → Br(K)`) gives `y = 0`.
`compactSupportMap_rootsOfUnityToSUnits_eq_zero` follows from the naturality of `H_c → H`
(`compactSupportMap_compactToGlobal`) and the exact sequence
`∏_{v ∈ S} H¹(K_v, K̄_vˣ) → H_c²(G_S, E) → H²(G_S, E)`, and `surjective_kummerCompactδ` from the long
exact sequence of `compactSupportδ` (`compactSupportCohomology_exact₁`).

## Declarations

In the order of the file:

- `maximalUnitsLocalHom` (def): The coefficient map `K_Sˣ → K̄_vˣ` of `ι` at a finite place `v`, a morphism of modules of `G_{K_v}`.
- `maximalUnitsLocalHom_hom_apply` (theorem).
- `sUnitsLocalHom` (def): The coefficient map `𝒪_{K_S,S}ˣ → K̄_vˣ` of `ι` at a finite place `v`.
- `sUnitsLocalHom_hom_apply` (theorem).
- `isSmoothRep_localKummerSequence_X₁` (instance).
- `isSmoothRep_localKummerSequence_X₂` (instance).
- `isSmoothRep_localKummerSequence_X₃` (instance).
- `kummerLocalMap` (def): The Kummer sequence of the `S`-units, restricted to `G_{K_v}`, maps to the local Kummer sequence: the identity on `μ_n` and `sUnitsLocalHom` on the units.
- `kummerLocalMap_τ₁` (theorem).
- `kummerLocalMap_τ₃` (theorem).
- `natCast_notMem_of_notMem` (theorem).
- `unitsCompact` (abbrev): The cohomology with compact support of the `S`-units, with the local modules `K̄_vˣ`.
- `kummerCompactδ` (def): **The Kummer connecting map with compact support** `H_c¹(G_S, 𝒪_Sˣ; (K̄_vˣ)_v) → H_c²(G_S, μ_n)`.
- `compactSupportMap_compactToGlobal` (theorem): `H_c → H` is natural in the coefficients.
- `eq_zero_realBrauerGroup_of_nsmul` (theorem): An `n`-torsion class of the Brauer group of a real or complex place is zero when `n` is odd or `K` is totally complex.
- `coeffMap_rootsOfUnityToSUnits_eq_zero` (theorem): A class of `H²(G_S, μ_n)` vanishing at the places of `S` maps to zero in `H²(G_S, 𝒪_Sˣ)`.
- `subsingleton_cohomology_one_localUnits` (theorem).
- `compactSupportMap_rootsOfUnityToSUnits_eq_zero` (theorem): `μ_n → 𝒪_Sˣ` induces zero on `H_c²`.
- `surjective_kummerCompactδ` (theorem): **The Kummer connecting map with compact support is surjective** for `n = ℓᵏ`, the places above `ℓ` in `S`, `n` odd or `K` totally complex.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseKummerDefs.lean`, `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseKummerDelta.lean` and `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseKummer.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's `localKummerSequence` (with `μ_n(K_S)` restricted to `G_{K_v}`), `compactSupportδ`, `compactSupportMap` and the Brauer group of `K` with its localizations (`brauerLocalization`, `maximalSUnitsInflation`) replace the source's local Kummer sequence with `μ_n(K̄_v)` and the comparison map between the two, `compactδ`, `compactCohomologyMap` and its `brauerLocal`, `sUnitsBrauer`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected printing (Springer, 2013), Chapter VIII, §3, Proposition (8.3.11), p. 458 (the cohomology of `𝒪_Sˣ`: `H¹(G_S, 𝒪_Sˣ)`
  is the `S`-class group, and `H²(G_S, 𝒪_Sˣ)(p)` is the kernel of the sum of the local invariants);
  Chapter VIII, §6, p. 482 (the exact sequence `0 → 𝒪_Sˣ → I_S → C_S → 0`).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge, 2006), Chapter II, §2, Remark 2.2, p. 165 (the exact sequence
  `0 → H²(U, G_m) → ⊕_{v ∈ S} Br(K_v) → ℚ/ℤ`).
