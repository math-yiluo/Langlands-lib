# Consequences of Poitou–Tate duality for `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/Corollaries.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

* `dualityEquiv`, `compactDualityEquiv`, `shaDualEquiv`: the isomorphisms
  `Hʳ(G_S, M) ≃ Ĥ_cˢ(G_S, M')^∨`, `Ĥ_cʳ(G_S, M) ≃ Hˢ(G_S, M')^∨` and `Ш¹(G_S, M) ≃ Ш²(G_S, M')^∨` given
  by `PoitouTate.IsDuality` and `PoitouTate.IsShaDuality`.
* `mem_range_loc_one_iff`, `mem_range_loc_two_iff`: from the nine-term exact sequence, a family of local
  classes in degree `1` (resp. `2`) comes from a global class if and only if it is orthogonal, for the
  sum of the local pairings, to the localizations of all global classes of `M'` in degree `1`
  (resp. `0`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.compactDualityEquiv.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hr : 1 ≤ r) :
  ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M r) ≃+
    (↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) s) →+
      Langlands.ProfiniteCohomology.QZ)
Langlands.GaloisCohomology.PoitouTate.compactDualityEquiv_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hr : 1 ≤ r)
  (x : ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M r)) :
  (Langlands.GaloisCohomology.PoitouTate.compactDualityEquiv hD h hr) x =
    (Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M h) x
Langlands.GaloisCohomology.PoitouTate.dualityEquiv.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
  ↑(Langlands.ProfiniteCohomology.cohomology M r) ≃+
    (↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι (Langlands.GaloisCohomology.PoitouTate.dual N M) s) →+
      ZMod N)
Langlands.GaloisCohomology.PoitouTate.dualityEquiv_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology M r)) :
  (Langlands.GaloisCohomology.PoitouTate.dualityEquiv hD h hs) x =
    (Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h) x
Langlands.GaloisCohomology.PoitouTate.mem_range_loc_one_iff.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hNT : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M)
  (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1) :
  ξ ∈ Set.range ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 1) ↔
    ∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 1)),
      ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) y = 0
Langlands.GaloisCohomology.PoitouTate.mem_range_loc_two_iff.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hNT : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M)
  (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 2) :
  ξ ∈ Set.range ⇑(Langlands.GaloisCohomology.PoitouTate.loc ι M 2) ↔
    ∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 0)),
      ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) y = 0
Langlands.GaloisCohomology.PoitouTate.shaDualEquiv.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M) :
  ↥(Langlands.GaloisCohomology.sha ι M 1) ≃+
    (↥(Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 2) →+
      Langlands.ProfiniteCohomology.QZ)
Langlands.GaloisCohomology.PoitouTate.shaDualEquiv_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (hD : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M)
  (x : ↥(Langlands.GaloisCohomology.sha ι M 1)) :
  (Langlands.GaloisCohomology.PoitouTate.shaDualEquiv hD) x = (Langlands.GaloisCohomology.PoitouTate.shaPairing ι N M) x
```

In degree one (namespace `Langlands.GaloisCohomology`): `connecting_locDual_one`: the connecting map
`H¹(G_S, M')^∨ → H²(G_S, M)` kills the image of `P¹(M)`; `leftOrthogonal_range_loc`: **the image of the
localization in degree one** is the orthogonal, for the sum of the local pairings `localTermPairing`, of
the image of the localization of `M'` (exactness of the nine-term sequence at `P¹(M)`).

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.connecting_locDual_one.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (ξ : Langlands.GaloisCohomology.PoitouTate.LocalTerm ι M 1) :
  (Langlands.GaloisCohomology.PoitouTate.connecting ι N M ⋯)
      ((Langlands.GaloisCohomology.PoitouTate.locDual ι N M ⋯) ξ) =
    0
Langlands.GaloisCohomology.leftOrthogonal_range_loc.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (hM : ∀ (m : ↑M), N • m = 0) :
  Langlands.ProfiniteCohomology.leftOrthogonal (Langlands.GaloisCohomology.localTermPairing ι N M)
      (Langlands.GaloisCohomology.PoitouTate.loc ι (Langlands.GaloisCohomology.PoitouTate.dual N M) 1).range =
    (Langlands.GaloisCohomology.PoitouTate.loc ι M 1).range
```

## Outline of the proofs

The isomorphisms are `AddEquiv.ofBijective` of the bijections of the structures; the annihilator description is the exactness `exact_loc_locDual_one`, `exact_loc_locDual_two` of `IsNineTermExact`.

## Declarations

`dualityEquiv`, `dualityEquiv_apply`, `compactDualityEquiv`, `compactDualityEquiv_apply`, `shaDualEquiv`, `shaDualEquiv_apply`, `mem_range_loc_one_iff`, `mem_range_loc_two_iff`, `connecting_locDual_one`, `leftOrthogonal_range_loc`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
