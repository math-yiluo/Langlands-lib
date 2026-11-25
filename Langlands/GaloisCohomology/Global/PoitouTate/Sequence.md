# The maps of the Poitou–Tate sequence for `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/Sequence.lean`, namespace `Langlands.GaloisCohomology.PoitouTate` (the last two
lemmas, `compactDualityMap_localToCompact` and `locDual_apply`, in `Langlands.GaloisCohomology`).

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω`, `N ≥ 1`, `μ_N = μ_N(K_S)` and, for a finite smooth
`G_S`-module `M`, `M' = Hom(M, μ_N)` (`dual`). This file defines the groups and maps of the
nine-term sequence of Poitou and Tate

`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M)
  → H⁰(G_S, M')^∨ → 0`

with `X^∨ = Hom(X, ℚ/ℤ)`:

* `LocalTerm ι M n = Pⁿ(M) = ∏_{v ∈ S} Hⁿ(K_v, M) × ∏_{w real} Hⁿ(K_w, M)` and, in degree `0`,
  `LocalTermHat ι M = P̂⁰(M)`, in which `H⁰(K_w, M)` is replaced by Tate's `Ĥ⁰(K_w, M)` at the real
  places;
* the localizations `loc ι M n` and `locHat ι M`;
* `locDual ι N M h` (`r + s = 2`) and `locDualHat ι N M`: the sum of the local pairings
  `Hʳ(K_v, M) × Hˢ(K_v, M') → H²(K_v, μ_N) → ℚ/ℤ` with the localizations of global classes;
* the cohomology with compact support `compactCohomology ι M n` of `G_S` with respect to the places
  of `S` and the real places, with Tate's `Ĥ⁰` in degree `0` at the real places, and the duality maps
  `compactDualityMap ι N M h : Ĥ_cʳ(G_S, M) → Hˢ(G_S, M')^∨` and
  `dualityMap ι N M h : Hʳ(G_S, M) → Hom(Ĥ_cˢ(G_S, M'), ℤ/N)` (`r + s = 3`), both given by the cup
  product with the evaluation `M ⊗ M' → μ_N` and the trace `Ĥ_c³(G_S, μ_N) → ℤ/N`;
* the connecting maps `connecting ι N M h : Hˢ(G_S, M')^∨ → Hʳ(G_S, M)` (`r + s = 3`): the inverse of
  `compactDualityMap` followed by `Ĥ_cʳ(G_S, M) → Hʳ(G_S, M)`. The definition takes no proof: it is
  `0` when `compactDualityMap` is not bijective, which never happens for `r ≥ 1` by the duality
  theorem;
* the pairing `shaPairing ι N M : Ш¹(M) × Ш²(M') → ℚ/ℤ` of the Tate–Shafarevich groups `sha` of
  `Langlands.GaloisCohomology.Global.Localization`;
* `locDual_apply`: `locDual` is the sum of the local pairings with the localizations, and
  `compactDualityMap_localToCompact`: on the image of the local terms, `compactDualityMap` is
  `locDual`.

All of these are the abstract maps of `Langlands.GaloisCohomology.CompactSupport.TateModified.NineTerm`
for the families `localFamily ι S`, `realFamily ι S`, the dualizing module `μ_N`, the trace `trace`
and the local invariants `invariantAt`, `realInvariantAt` of `Langlands.GaloisCohomology.Global.PoitouTate.Trace`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.LocalTerm.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) : Type u
Langlands.GaloisCohomology.PoitouTate.LocalTermHat.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  Type u
Langlands.GaloisCohomology.PoitouTate.compactCohomology.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) : ModuleCat (ULift.{u, 0} ℤ)
Langlands.GaloisCohomology.PoitouTate.compactDualityMap.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] {r s : ℕ} (h : r + s = 3) :
  ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M r) →+
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) s) →+
      Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.compactToGlobal.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) :
  ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M n) →+ ↑(Langlands.ProfiniteCohomology.cohomology M n)
Langlands.GaloisCohomology.PoitouTate.connecting.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] {r s : ℕ} (h : r + s = 3) :
  (↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) s) →+
      Langlands.ProfiniteCohomology.QZ) →+
    ↑(Langlands.ProfiniteCohomology.cohomology M r)
Langlands.GaloisCohomology.PoitouTate.connecting_compactDualityMap.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] {r s : ℕ} (h : r + s = 3)
  (hb : Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M h))
  (x : ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M r)) :
  (Langlands.GaloisCohomology.PoitouTate.connecting ι N M h)
      ((Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M h) x) =
    (Langlands.GaloisCohomology.PoitouTate.compactToGlobal ι M r) x
Langlands.GaloisCohomology.PoitouTate.dual.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) :
  Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
Langlands.GaloisCohomology.PoitouTate.dualityMap.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] {r s : ℕ} (h : r + s = 3) :
  ↑(Langlands.ProfiniteCohomology.cohomology M r) →+
    ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι (Langlands.GaloisCohomology.PoitouTate.dual N M) s) →+
      ZMod N
Langlands.GaloisCohomology.PoitouTate.exact_compactToGlobal_loc.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.compactToGlobal ι M (n + 1))
    ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M (n + 1))
Langlands.GaloisCohomology.PoitouTate.exact_locHat_localHatToCompact.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.locHat ι M)
    ⇑(Langlands.GaloisCohomology.PoitouTate.localHatToCompact ι M)
Langlands.GaloisCohomology.PoitouTate.exact_loc_localToCompact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M (n + 1))
    ⇑(Langlands.GaloisCohomology.PoitouTate.localToCompact ι M (n + 1))
Langlands.GaloisCohomology.PoitouTate.exact_localHatToCompact_compactToGlobal.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.localHatToCompact ι M)
    ⇑(Langlands.GaloisCohomology.PoitouTate.compactToGlobal ι M 1)
Langlands.GaloisCohomology.PoitouTate.exact_localToCompact_compactToGlobal.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) :
  Function.Exact ⇑(Langlands.GaloisCohomology.PoitouTate.localToCompact ι M n)
    ⇑(Langlands.GaloisCohomology.PoitouTate.compactToGlobal ι M (n + 1))
Langlands.GaloisCohomology.PoitouTate.finite_localModule.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Finite ↑M]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Finite ↑(Langlands.GaloisCohomology.localModule ι M v)
Langlands.GaloisCohomology.PoitouTate.finite_realLocalModule.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Finite ↑M]
  (w : NumberField.InfinitePlace K) : Finite ↑(Langlands.GaloisCohomology.realLocalModule ι M w)
Langlands.GaloisCohomology.PoitouTate.hatMk.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 0 →+ Langlands.GaloisCohomology.PoitouTate.LocalTermHat ι M
Langlands.GaloisCohomology.PoitouTate.hatMk_surjective.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.hatMk ι M)
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_dual.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] : Langlands.IsSmoothRep (Langlands.GaloisCohomology.PoitouTate.dual N M)
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_localModule_dual.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.localModule ι
      (Langlands.ProfiniteCohomology.dualRep (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M) v)
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_realLocalModule_dual.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (w : NumberField.InfinitePlace K) :
  Langlands.IsSmoothRep
    (Langlands.GaloisCohomology.realLocalModule ι
      (Langlands.ProfiniteCohomology.dualRep (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M) w)
Langlands.GaloisCohomology.PoitouTate.loc.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) : ↑(Langlands.ProfiniteCohomology.cohomology M n) →+ Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M n
Langlands.GaloisCohomology.PoitouTate.locDual.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] {r s : ℕ} (h : r + s = 2) :
  Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M r →+
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) s) →+
      Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.locDualHat.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] :
  Langlands.GaloisCohomology.PoitouTate.LocalTermHat ι M →+
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 2) →+
      Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.locDualHat_hatMk.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 0) :
  (Langlands.GaloisCohomology.PoitouTate.locDualHat ι N M) ((Langlands.GaloisCohomology.PoitouTate.hatMk ι M) ξ) =
    (Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ
Langlands.GaloisCohomology.PoitouTate.locHat.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  ↑(Langlands.ProfiniteCohomology.cohomology M 0) →+ Langlands.GaloisCohomology.PoitouTate.LocalTermHat ι M
Langlands.GaloisCohomology.PoitouTate.locHat_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology M 0)) :
  (Langlands.GaloisCohomology.PoitouTate.locHat ι M) x =
    (Langlands.GaloisCohomology.PoitouTate.hatMk ι M) ((Langlands.GaloisCohomology.PoitouTate.loc ι M 0) x)
Langlands.GaloisCohomology.PoitouTate.loc_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) (x : ↑(Langlands.ProfiniteCohomology.cohomology M n)) :
  (Langlands.GaloisCohomology.PoitouTate.loc ι M n) x =
    (fun v => (Langlands.GaloisCohomology.localization ι M (↑v) n) x, fun w =>
      (Langlands.GaloisCohomology.realLocalization ι M (↑w) n) x)
Langlands.GaloisCohomology.PoitouTate.loc_eq_zero_iff.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  {n : ℕ} (x : ↑(Langlands.ProfiniteCohomology.cohomology M n)) :
  (Langlands.GaloisCohomology.PoitouTate.loc ι M n) x = 0 ↔
    (∀ (v : ↑S), (Langlands.GaloisCohomology.localization ι M (↑v) n) x = 0) ∧
      ∀ (w : { w // w.IsReal }), (Langlands.GaloisCohomology.realLocalization ι M (↑w) n) x = 0
Langlands.GaloisCohomology.PoitouTate.localHatToCompact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M] :
  Langlands.GaloisCohomology.PoitouTate.LocalTermHat ι M →+
    ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M 1)
Langlands.GaloisCohomology.PoitouTate.localToCompact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) :
  Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M n →+
    ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M (n + 1))
Langlands.GaloisCohomology.PoitouTate.mem_sha_iff_loc_eq_zero.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  {n : ℕ} (x : ↑(Langlands.ProfiniteCohomology.cohomology M n)) :
  x ∈ Langlands.GaloisCohomology.sha ι M n ↔ (Langlands.GaloisCohomology.PoitouTate.loc ι M n) x = 0
Langlands.GaloisCohomology.PoitouTate.shaPairing.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] :
  ↥(Langlands.GaloisCohomology.sha ι M 1) →+
    ↥(Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 2) →+
      Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.shaPairing_compactToGlobal.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Finite ↑S] (x : ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M 1))
  (hx : (Langlands.GaloisCohomology.PoitouTate.compactToGlobal ι M 1) x ∈ Langlands.GaloisCohomology.sha ι M 1)
  (y : ↥(Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 2)) :
  ((Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M)
        ⟨(Langlands.GaloisCohomology.PoitouTate.compactToGlobal ι M 1) x, hx⟩)
      y =
    ((Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M ⋯) x) ↑y
Langlands.GaloisCohomology.PoitouTate.sha_eq_ptTSha.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (n : ℕ) :
  Langlands.GaloisCohomology.sha ι M n =
    Langlands.GaloisCohomology.ptTSha (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.realFamily ι S) M n
Langlands.GaloisCohomology.compactDualityMap_localToCompact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N] [Finite ↑S]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
  (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M r) :
  (Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M h')
      ((Langlands.GaloisCohomology.PoitouTate.localToCompact ι M r) ξ) =
    (Langlands.GaloisCohomology.PoitouTate.locDual ι N M h) ξ
Langlands.GaloisCohomology.locDual_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [Finite ↑S]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Finite ↑M]
  [Langlands.IsSmoothRep M] {r s : ℕ} (h : r + s = 2) (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M r)
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) s)) :
  ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M h) ξ) y =
    ∑ v,
        ((Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
              (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) v h)
            (ξ.1 v))
          ((Langlands.GaloisCohomology.ptRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.dual N M) v s)
            y) +
      ∑ w,
        ((Langlands.GaloisCohomology.ptLocalPairing (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) M
              (fun w => Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w) w h)
            (ξ.2 w))
          ((Langlands.GaloisCohomology.ptRes (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.dual N M) w s)
            y)
```

Also: `PoitouTate.subsingleton_cohomology_localModule_of_three_le`: at a finite place, a module killed
by `n ≠ 0` has no cohomology in degrees `≥ 3` (`Local.subsingleton_cohomology_of_three_le`); the
instances `instFiniteDualizingModule` (`μ_N(K_S)` is finite) and `instFiniteDual` (`M' = Hom(M, μ_N)` is
finite).

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.subsingleton_cohomology_localModule_of_three_le.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ} (hn : n ≠ 0)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (hM : ∀ (m : ↑M), n • m = 0) {r : ℕ} (hr : 3 ≤ r) :
  Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) r)
Langlands.GaloisCohomology.instFiniteDualizingModule.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (N : ℕ) [NeZero N] :
  Finite ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
Langlands.GaloisCohomology.instFiniteDual.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (N : ℕ)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Finite ↑M] [NeZero N] :
  Finite ↑(Langlands.GaloisCohomology.PoitouTate.dual N M)
```

## Outline of the proofs

Definitions only: the maps of the Tate-modified nine-term sequence of the abstract layer (`ptT*` of `CompactSupport/TateModified/NineTerm.lean`) for the families `localFamily ι S`, `realFamily ι S` and the dualizing module `μ_N`, with the lemmas that unfold them. `locDual_apply` is `ptTLocalDualMap_apply`. `compactDualityMap_localToCompact`: the cup product of the image of a local class with a global class is the family of the local cup products (`tateCompactCupRes_ptTLocalToCompact`), on which the trace is the sum of the local invariants (`trace_localToCompact`, `sumInvariants_apply`).

## Declarations

`finite_localModule`, `finite_realLocalModule`, `LocalTerm`, `LocalTermHat`, `loc`, `loc_apply`, `loc_eq_zero_iff`, `locHat`, `hatMk`, `hatMk_surjective`, `locHat_apply`, `compactCohomology`, `compactToGlobal`, `localToCompact`, `localHatToCompact`, `exact_compactToGlobal_loc`, `exact_loc_localToCompact`, `exact_localToCompact_compactToGlobal`, `exact_locHat_localHatToCompact`, `exact_localHatToCompact_compactToGlobal`, `mem_sha_iff_loc_eq_zero`, `sha_eq_ptTSha`, `dual`, `isSmoothRep_dual`, `isSmoothRep_localModule_dual`, `isSmoothRep_realLocalModule_dual`, `locDual`, `locDualHat`, `locDualHat_hatMk`, `compactDualityMap`, `dualityMap`, `connecting`, `connecting_compactDualityMap`, `shaPairing`, `shaPairing_compactToGlobal`, `compactDualityMap_localToCompact`, `locDual_apply`, `subsingleton_cohomology_localModule_of_three_le`, `instFiniteDualizingModule`, `instFiniteDual`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
